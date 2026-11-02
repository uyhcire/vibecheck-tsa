# Print raw HID input reports from the HOTAS One for a few seconds.
import ctypes, ctypes.util, sys, time
iokit = ctypes.cdll.LoadLibrary(ctypes.util.find_library("IOKit"))
cf = ctypes.cdll.LoadLibrary(ctypes.util.find_library("CoreFoundation"))
cf.CFRunLoopGetCurrent.restype = ctypes.c_void_p
cf.CFRunLoopRunInMode.argtypes = [ctypes.c_void_p, ctypes.c_double, ctypes.c_bool]
kCFRunLoopDefaultMode = ctypes.c_void_p.in_dll(cf, "kCFRunLoopDefaultMode")
cf.CFNumberCreate.restype = ctypes.c_void_p
cf.CFStringCreateWithCString.restype = ctypes.c_void_p
cf.CFDictionaryCreateMutable.restype = ctypes.c_void_p
cf.CFDictionarySetValue.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]
iokit.IOHIDManagerCreate.restype = ctypes.c_void_p
iokit.IOHIDManagerSetDeviceMatching.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
iokit.IOHIDManagerOpen.argtypes = [ctypes.c_void_p, ctypes.c_uint32]
iokit.IOHIDManagerScheduleWithRunLoop.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]
CB = ctypes.CFUNCTYPE(None, ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p, ctypes.c_uint32, ctypes.c_uint32, ctypes.POINTER(ctypes.c_uint8), ctypes.c_long)
iokit.IOHIDManagerRegisterInputReportCallback.argtypes = [ctypes.c_void_p, CB, ctypes.c_void_p]

def cfnum(v):
    n = ctypes.c_int32(v)
    return cf.CFNumberCreate(None, 3, ctypes.byref(n))  # kCFNumberSInt32Type
def cfstr(s): return cf.CFStringCreateWithCString(None, s.encode(), 0x08000100)
m = cf.CFDictionaryCreateMutable(None, 0, None, None)
cf.CFDictionarySetValue(m, cfstr("VendorID"), cfnum(0x044f))
cf.CFDictionarySetValue(m, cfstr("ProductID"), cfnum(0xb68d))

last = {}
def cb(ctx, res, sender, rtype, rid, report, length):
    b = bytes(report[:length])
    if last.get(rid) != b:
        last[rid] = b
        o = 1 if b[0] == rid else 0  # macOS prepends the report ID byte
        x = b[o] | (b[o+1] << 8); y = b[o+2] | (b[o+3] << 8)
        print(f"rid={rid} len={length} X={x} Y={y} Z={b[o+4]} Rz={b[o+5]} Rx={b[o+6]} Ry={b[o+7]} Slider={b[o+8]} Dial={b[o+9]} hat={b[o+10]&0x0f} btns={b[o+10]>>4 | b[o+11]<<4:#06x}", flush=True)
cbp = CB(cb)
mgr = iokit.IOHIDManagerCreate(None, 0)
iokit.IOHIDManagerSetDeviceMatching(mgr, m)
iokit.IOHIDManagerRegisterInputReportCallback(mgr, cbp, None)
iokit.IOHIDManagerScheduleWithRunLoop(mgr, cf.CFRunLoopGetCurrent(), kCFRunLoopDefaultMode)
print("open:", iokit.IOHIDManagerOpen(mgr, 0))
end = time.time() + float(sys.argv[1] if len(sys.argv) > 1 else 4)
while time.time() < end:
    cf.CFRunLoopRunInMode(kCFRunLoopDefaultMode, 0.1, False)

# Snapshot of the current input report (works without movement).
iokit.IOHIDManagerCopyDevices.restype = ctypes.c_void_p
iokit.IOHIDManagerCopyDevices.argtypes = [ctypes.c_void_p]
cf.CFSetGetCount.argtypes = [ctypes.c_void_p]; cf.CFSetGetCount.restype = ctypes.c_long
cf.CFSetGetValues.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p)]
iokit.IOHIDDeviceGetReport.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_long, ctypes.POINTER(ctypes.c_uint8), ctypes.POINTER(ctypes.c_long)]
devs = iokit.IOHIDManagerCopyDevices(mgr)
if devs:
    n = cf.CFSetGetCount(devs); arr = (ctypes.c_void_p * n)(); cf.CFSetGetValues(devs, arr)
    buf = (ctypes.c_uint8 * 64)(); ln = ctypes.c_long(64)
    r = iokit.IOHIDDeviceGetReport(arr[0], 0, 1, buf, ctypes.byref(ln))
    b = bytes(buf[:ln.value]); print("getreport rc=%d len=%d raw=%s" % (r, ln.value, b.hex()))
    o = 1 if b and b[0] == 1 and ln.value >= 12 else 0  # skip report-id byte if present
    x = b[o] | (b[o+1] << 8); y = b[o+2] | (b[o+3] << 8)
    print(f"SNAPSHOT X={x} Y={y} Z={b[o+4]} Rz={b[o+5]} Rx={b[o+6]} Ry={b[o+7]} Slider={b[o+8]} Dial={b[o+9]} hat={b[o+10]&0xf}")
