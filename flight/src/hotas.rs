//! Thrustmaster T.Flight HOTAS One read straight over HID (macOS IOKit, no crates).
//!
//! A port of John's `sidecar/hotas_hid.py` (branch `john/xplane-jsbsim`); setup notes are in
//! `hardware/hotas-one/README.md`. The base switch must be on PC when the cable goes in (USB id
//! 044f:b68d): in Xbox mode macOS sees no joystick. The stick sends a report only when a control
//! moves, so `Hotas::get` is `None` until it has been touched once, and again after it is unplugged.

use std::sync::{Arc, Mutex};

pub const VID: i32 = 0x044F;
pub const PID: i32 = 0xB68D;

/// The stick button labelled 2 (USB button 4): safety filter on / off, as in John's sidecar.
pub const BTN_FILTER: u16 = 1 << 3;
/// USB button 3: kamikaze autopilot on / off, as in John's sidecar.
pub const BTN_KAMIKAZE: u16 = 1 << 2;

/// One decoded input report.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Sticks {
    /// Stick fore/aft, -1..1, +1 = pulled back (nose up).
    pub pitch: f64,
    /// Stick left/right, -1..1, +1 = right.
    pub roll: f64,
    /// Twist grip, -1..1.
    pub yaw: f64,
    /// Lever, 0 at idle to 1 at full.
    pub throttle: f64,
    /// Bit i = USB button i + 1 held (1 = trigger).
    pub buttons: u16,
}

/// Report 1 after the report-id byte: X, Y as 10-bit little-endian, then Z (lever, 255 at idle),
/// Rz (twist), Rx, Ry, Slider, Dial as bytes, then the hat nibble and the buttons.
pub fn decode(b: &[u8; 12]) -> Sticks {
    let x = u16::from_le_bytes([b[0], b[1]]) as f64;
    let y = u16::from_le_bytes([b[2], b[3]]) as f64;
    Sticks {
        roll: ((x - 512.0) / 511.5).clamp(-1.0, 1.0),
        pitch: ((y - 512.0) / 511.5).clamp(-1.0, 1.0),
        throttle: (255.0 - b[4] as f64) / 255.0,
        yaw: ((b[5] as f64 - 128.0) / 127.5).clamp(-1.0, 1.0),
        buttons: (b[10] >> 4) as u16 | (b[11] as u16) << 4,
    }
}

/// Zero inside the dead zone, then rescale so the full travel still reaches 1.
pub fn deadzone(v: f64, dz: f64) -> f64 {
    if v.abs() < dz {
        0.0
    } else {
        (v.abs() - dz) / (1.0 - dz) * v.signum()
    }
}

/// The latest report, kept by a listener thread with its own run loop (the window's is left alone).
pub struct Hotas {
    latest: Arc<Mutex<Option<Sticks>>>,
}

impl Hotas {
    /// Start listening. Never fails: with no stick (or not on macOS) `get` stays `None`.
    pub fn open() -> Hotas {
        let latest = Arc::new(Mutex::new(None));
        let ctx = Arc::clone(&latest);
        let _ = std::thread::Builder::new().name("hotas".into()).spawn(move || listen(ctx));
        Hotas { latest }
    }

    /// The last report, or `None` before the first one and after the stick is unplugged.
    pub fn get(&self) -> Option<Sticks> {
        *self.latest.lock().unwrap()
    }
}

#[cfg(target_os = "macos")]
fn listen(latest: Arc<Mutex<Option<Sticks>>>) {
    use std::ffi::c_void;
    use std::ptr::null;
    type CFIndex = isize;
    type CFTypeRef = *const c_void;

    #[link(name = "CoreFoundation", kind = "framework")]
    extern "C" {
        static kCFRunLoopDefaultMode: CFTypeRef;
        // CFDictionaryKeyCallBacks / CFDictionaryValueCallBacks: only their addresses are used.
        static kCFTypeDictionaryKeyCallBacks: [usize; 6];
        static kCFTypeDictionaryValueCallBacks: [usize; 5];
        fn CFRunLoopGetCurrent() -> *mut c_void;
        fn CFRunLoopRun();
        fn CFStringCreateWithCString(alloc: CFTypeRef, s: *const std::ffi::c_char, encoding: u32) -> CFTypeRef;
        fn CFNumberCreate(alloc: CFTypeRef, ty: CFIndex, v: *const c_void) -> CFTypeRef;
        fn CFDictionaryCreateMutable(alloc: CFTypeRef, cap: CFIndex, k: *const [usize; 6], v: *const [usize; 5]) -> *mut c_void;
        fn CFDictionarySetValue(d: *mut c_void, k: CFTypeRef, v: CFTypeRef);
        fn CFRelease(x: CFTypeRef);
    }
    type ReportCb = extern "C" fn(*mut c_void, i32, *mut c_void, u32, u32, *mut u8, CFIndex);
    type DeviceCb = extern "C" fn(*mut c_void, i32, *mut c_void, *mut c_void);
    #[link(name = "IOKit", kind = "framework")]
    extern "C" {
        fn IOHIDManagerCreate(alloc: CFTypeRef, options: u32) -> *mut c_void;
        fn IOHIDManagerSetDeviceMatching(m: *mut c_void, matching: *const c_void);
        fn IOHIDManagerRegisterInputReportCallback(m: *mut c_void, cb: ReportCb, ctx: *mut c_void);
        fn IOHIDManagerRegisterDeviceRemovalCallback(m: *mut c_void, cb: DeviceCb, ctx: *mut c_void);
        fn IOHIDManagerScheduleWithRunLoop(m: *mut c_void, rl: *mut c_void, mode: CFTypeRef);
        fn IOHIDManagerOpen(m: *mut c_void, options: u32) -> i32;
    }

    extern "C" fn on_report(ctx: *mut c_void, _res: i32, _dev: *mut c_void, _ty: u32, id: u32, report: *mut u8, len: CFIndex) {
        let latest = unsafe { &*(ctx as *const Mutex<Option<Sticks>>) };
        let b = unsafe { std::slice::from_raw_parts(report, len.max(0) as usize) };
        let o = usize::from(b.first() == Some(&(id as u8))); // macOS prepends the report-id byte
        if let Some(r) = b.get(o..o + 12) {
            *latest.lock().unwrap() = Some(decode(r.try_into().unwrap()));
        }
    }
    extern "C" fn on_removed(ctx: *mut c_void, _res: i32, _sender: *mut c_void, _dev: *mut c_void) {
        let latest = unsafe { &*(ctx as *const Mutex<Option<Sticks>>) };
        *latest.lock().unwrap() = None;
    }

    unsafe {
        let match_on = CFDictionaryCreateMutable(null(), 0, &kCFTypeDictionaryKeyCallBacks, &kCFTypeDictionaryValueCallBacks);
        for (key, v) in [(c"VendorID", VID), (c"ProductID", PID)] {
            let k = CFStringCreateWithCString(null(), key.as_ptr(), 0x0800_0100); // UTF-8
            let n = CFNumberCreate(null(), 3, &v as *const i32 as *const c_void); // SInt32
            CFDictionarySetValue(match_on, k, n);
            CFRelease(k);
            CFRelease(n);
        }
        let mgr = IOHIDManagerCreate(null(), 0);
        IOHIDManagerSetDeviceMatching(mgr, match_on);
        CFRelease(match_on);
        // The callbacks' context: this thread runs for the life of the process, so the Arc is never released.
        let ctx = Arc::into_raw(latest) as *mut c_void;
        IOHIDManagerRegisterInputReportCallback(mgr, on_report, ctx);
        IOHIDManagerRegisterDeviceRemovalCallback(mgr, on_removed, ctx);
        IOHIDManagerScheduleWithRunLoop(mgr, CFRunLoopGetCurrent(), kCFRunLoopDefaultMode);
        let r = IOHIDManagerOpen(mgr, 0);
        if r != 0 {
            eprintln!("HOTAS: could not open HID (IOReturn {r:#x}); keyboard only");
            return;
        }
        loop {
            CFRunLoopRun();
            std::thread::sleep(std::time::Duration::from_secs(1));
        }
    }
}

#[cfg(not(target_os = "macos"))]
fn listen(_: Arc<Mutex<Option<Sticks>>>) {}

#[cfg(test)]
mod tests {
    use super::*;

    // John's selftest in `hotas_hid.py`, byte for byte.
    #[test]
    fn decode_reports() {
        let h = decode(&[0x00, 0x02, 0x00, 0x02, 255, 128, 255, 255, 128, 128, 0x08, 0x00]); // all at rest
        assert!(h.pitch.abs() < 0.01 && h.roll.abs() < 0.01 && h.throttle == 0.0 && h.yaw.abs() < 0.01 && h.buttons & 1 == 0);
        let h = decode(&[0xFF, 0x03, 0x00, 0x00, 0, 255, 255, 255, 128, 128, 0x18, 0x00]); // full right, full fwd, full thr
        assert!(h.roll > 0.99 && h.pitch < -0.99 && h.throttle == 1.0 && h.yaw > 0.99 && h.buttons & 1 != 0);
        let h = decode(&[0x00, 0x02, 0x00, 0x02, 255, 128, 255, 255, 128, 128, 0x28, 0x01]); // buttons 2 and 5
        assert_eq!(h.buttons, 0b10010);
        assert!(h.pitch >= -1.0 && h.roll <= 1.0);
    }

    // John's `deadzone` checks in `xplane_jsbsim.py`.
    #[test]
    fn deadzone_rescales() {
        assert_eq!(deadzone(0.1, 0.15), 0.0);
        assert_eq!(deadzone(1.0, 0.15), 1.0);
        assert!((deadzone(-0.575, 0.15) + 0.5).abs() < 1e-9);
    }

    // With the stick plugged in, move the controls while this runs (`HOTAS_SECS`, default 15 s):
    // cargo test --release --bin cityflight hotas::tests::live -- --ignored --nocapture
    #[test]
    #[ignore]
    fn live() {
        let h = Hotas::open();
        let mut last = None;
        let secs = std::env::var("HOTAS_SECS").ok().and_then(|s| s.parse().ok()).unwrap_or(15);
        let end = std::time::Instant::now() + std::time::Duration::from_secs(secs);
        while std::time::Instant::now() < end {
            let s = h.get();
            if s != last {
                println!("{s:.2?}");
                last = s;
            }
            std::thread::sleep(std::time::Duration::from_millis(20));
        }
    }
}
