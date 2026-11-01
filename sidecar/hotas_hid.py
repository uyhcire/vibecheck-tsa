"""Read a Thrustmaster T.Flight HOTAS One directly over HID on macOS (IOKit via ctypes, no packages).

Report 1 layout (after the report-id byte macOS prepends): X, Y as 10-bit little-endian,
then Z (throttle lever, 255 at idle), Rz (twist), Rx, Ry, Slider, Dial as bytes, hat nibble + 15 buttons.
"""
import ctypes
import ctypes.util

VID, PID = 0x044F, 0xB68D


def _lib(name):
    return ctypes.cdll.LoadLibrary(ctypes.util.find_library(name))


class Hotas:
    """Latest stick state; call poll() once per frame on the thread that created it."""

    def __init__(self):
        self.pitch = self.roll = self.yaw = 0.0   # -1..1, pitch +1 = stick back
        self.throttle = 0.0                      # 0..1
        self.trigger = False
        self.buttons = 0        # bit i = button i+1 held (1 = trigger)
        self.seen = False
        cf, iokit = _lib("CoreFoundation"), _lib("IOKit")
        self._cf = cf
        cf.CFRunLoopGetCurrent.restype = ctypes.c_void_p
        cf.CFRunLoopRunInMode.argtypes = [ctypes.c_void_p, ctypes.c_double, ctypes.c_bool]
        cf.CFNumberCreate.restype = ctypes.c_void_p
        cf.CFStringCreateWithCString.restype = ctypes.c_void_p
        cf.CFDictionaryCreateMutable.restype = ctypes.c_void_p
        cf.CFDictionarySetValue.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]
        iokit.IOHIDManagerCreate.restype = ctypes.c_void_p
        iokit.IOHIDManagerSetDeviceMatching.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        iokit.IOHIDManagerOpen.argtypes = [ctypes.c_void_p, ctypes.c_uint32]
        iokit.IOHIDManagerScheduleWithRunLoop.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]
        self._mode = ctypes.c_void_p.in_dll(cf, "kCFRunLoopDefaultMode")
        CB = ctypes.CFUNCTYPE(None, ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p, ctypes.c_uint32,
                              ctypes.c_uint32, ctypes.POINTER(ctypes.c_uint8), ctypes.c_long)
        iokit.IOHIDManagerRegisterInputReportCallback.argtypes = [ctypes.c_void_p, CB, ctypes.c_void_p]

        def num(v):
            n = ctypes.c_int32(v)
            return cf.CFNumberCreate(None, 3, ctypes.byref(n))

        def cstr(s):
            return cf.CFStringCreateWithCString(None, s.encode(), 0x08000100)

        match = cf.CFDictionaryCreateMutable(None, 0, None, None)
        cf.CFDictionarySetValue(match, cstr("VendorID"), num(VID))
        cf.CFDictionarySetValue(match, cstr("ProductID"), num(PID))
        self._cb = CB(self._on_report)  # keep a reference or ctypes frees it
        mgr = iokit.IOHIDManagerCreate(None, 0)
        iokit.IOHIDManagerSetDeviceMatching(mgr, match)
        iokit.IOHIDManagerRegisterInputReportCallback(mgr, self._cb, None)
        iokit.IOHIDManagerScheduleWithRunLoop(mgr, cf.CFRunLoopGetCurrent(), self._mode)
        if iokit.IOHIDManagerOpen(mgr, 0) != 0:
            raise RuntimeError("could not open the HOTAS (is the base switch on PC and the cable in?)")
        self._mgr = mgr

    def _on_report(self, ctx, res, sender, rtype, rid, report, length):
        b = bytes(report[:length])
        o = 1 if b and b[0] == rid else 0
        if length < o + 12:
            return
        self.decode(b[o:o + 12])
        self.seen = True

    def decode(self, b):
        x = b[0] | (b[1] << 8)
        y = b[2] | (b[3] << 8)
        self.roll = (x - 512) / 511.5
        self.pitch = (y - 512) / 511.5
        self.throttle = (255 - b[4]) / 255
        self.yaw = (b[5] - 128) / 127.5
        self.buttons = (b[10] >> 4) | (b[11] << 4)
        self.trigger = bool(self.buttons & 1)

    def poll(self):
        """Process pending reports without blocking."""
        self._cf.CFRunLoopRunInMode(self._mode, 0.001, True)
        return self.pitch, self.roll, self.yaw, self.throttle


def selftest():
    h = Hotas.__new__(Hotas)
    h.decode(bytes([0x00, 0x02, 0x00, 0x02, 255, 128, 255, 255, 128, 128, 0x08, 0x00]))  # all at rest
    assert abs(h.pitch) < 0.01 and abs(h.roll) < 0.01 and h.throttle == 0 and abs(h.yaw) < 0.01 and not h.trigger
    h.decode(bytes([0xFF, 0x03, 0x00, 0x00, 0, 255, 255, 255, 128, 128, 0x18, 0x00]))  # full right, full fwd, full thr
    assert h.roll > 0.99 and h.pitch < -0.99 and h.throttle == 1 and h.yaw > 0.99 and h.trigger
    h.decode(bytes([0x00, 0x02, 0x00, 0x02, 255, 128, 255, 255, 128, 128, 0x28, 0x01]))  # buttons 2 and 5
    assert h.buttons == 0b10010 and not h.trigger
    print("hotas_hid selftest ok")


if __name__ == "__main__":
    selftest()
