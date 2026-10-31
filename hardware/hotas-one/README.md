# Thrustmaster T.Flight HOTAS One on macOS

Notes from getting the stick to drive X-Plane 12 and this sim on an Apple Silicon Mac. No driver is needed.

## The one thing that matters: the PC/Xbox switch

| Switch | USB id | What macOS sees | Usable |
| --- | --- | --- | --- |
| Xbox | `044f:b68c` | vendor-specific device (Xbox GIP), no joystick | no |
| PC | `044f:b68d` | standard HID joystick, built-in driver | yes |

The mode is latched when the cable is plugged in: set the switch to **PC** first, then connect. Check with:

```
hidutil list | grep -i hotas        # expect PID 0xb68d, UsagePage 1, Usage 4
```

If nothing shows, check the hub's cable to the Mac before anything else.

## Axes

The HID report carries 8 axes, a hat and 15 buttons. Only five axes have hardware behind them. Hosts number them differently:

| Control | HID usage | Rest value | X-Plane 12 (macOS) axis | SDL3 axis |
| --- | --- | --- | --- | --- |
| stick left/right (roll) | X | 512 / 1023 | 0 | 0 |
| stick fwd/back (pitch) | Y | 512 / 1023 | 1 | 1 |
| throttle lever | Z | 255 at idle, 0 at full | 2 | 2 |
| twist grip (yaw) | Rz | 128 | 3 | 5 |
| rocker paddle (throttle back) | Dial | 128 | 7 | 7 |
| unused | Rx, Ry, Slider | constant | 4, 5, 6 | 3, 4, 6 |

X-Plane numbers axes in report-descriptor order; SDL sorts them by HID usage. The lever reads full scale at idle, so throttle = (1 − z) / 2 from SDL's [−1, 1] value.

`hid_sample.py` prints the raw reports while you move the controls (`python3 -I hid_sample.py 30`). The device only sends a report when something changes.

## X-Plane 12

Copy `T.Flight Hotas One - Mac.joy` into `<X-Plane 12>/Resources/joystick configs/`. X-Plane reads it the first time it sees the device and assigns roll, pitch, throttle, rudder (twist) and the hat; after that it uses its own saved preferences, so later changes go through Settings > Joystick. Run the calibration when prompted. If the throttle moves the wrong way for you, tick Reverse on axis 2 in Settings > Joystick; adjust pitch and roll feel under Control Sensitivity.

## This sim

`App/Game.lean` reads SDL axis 1 (pitch) and 2 (throttle), button 0 (trigger) brakes. Other sticks: `VC_JOY_PITCH` and `VC_JOY_THR` select the axes.
