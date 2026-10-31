namespace Gfx

@[extern "fs_init"] opaque init (w h : UInt32) (title : @& String) : IO Bool
@[extern "fs_quit"] opaque quit : IO Unit
@[extern "fs_poll"] opaque poll : IO UInt32
@[extern "fs_color"] opaque color (r g b a : UInt8) : IO Unit
@[extern "fs_clear"] opaque clear : IO Unit
@[extern "fs_present"] opaque present : IO Unit
@[extern "fs_line"] opaque line (x1 y1 x2 y2 : Float) : IO Unit
@[extern "fs_rect"] opaque rect (x y w h : Float) (fill : UInt8) : IO Unit
@[extern "fs_tri"] opaque tri (x1 y1 x2 y2 x3 y3 : Float) : IO Unit
@[extern "fs_text"] opaque text (x y scale : Float) (s : @& String) : IO Unit
/-- Nanoseconds since SDL start. -/
@[extern "fs_ticks"] opaque ticks : IO UInt64
/-- Save the next presented frame as a BMP. -/
@[extern "fs_screenshot"] opaque screenshot (path : @& String) : IO Unit
@[extern "fs_delay"] opaque delay (ms : UInt32) : IO Unit
/-- Joystick axis `i` as of the last `poll`, in [-1, 1]; NaN when no joystick is connected.
SDL numbers axes by HID usage: 0 X, 1 Y (stick pitch), 2 Z (T.Flight throttle lever). -/
@[extern "fs_joy_axis"] opaque joyAxis (i : UInt32) : IO Float

def keyUp : UInt32 := 1
def keyDown : UInt32 := 2
def keyThrUp : UInt32 := 4
def keyThrDn : UInt32 := 8
def keyBrake : UInt32 := 16
def pFilter : UInt32 := (1 : UInt32) <<< 16
def pRestart : UInt32 := (1 : UInt32) <<< 17
def pPause : UInt32 := (1 : UInt32) <<< 18
def pGhost : UInt32 := (1 : UInt32) <<< 19
def pQuit : UInt32 := (1 : UInt32) <<< 20
def pHelp : UInt32 := (1 : UInt32) <<< 21
def pFast : UInt32 := (1 : UInt32) <<< 22
def pAuto : UInt32 := (1 : UInt32) <<< 23

def has (k bit : UInt32) : Bool := k &&& bit != 0

def fillRect (x y w h : Float) : IO Unit := rect x y w h 1

def quad (x1 y1 x2 y2 x3 y3 x4 y4 : Float) : IO Unit := do
  tri x1 y1 x2 y2 x3 y3
  tri x1 y1 x3 y3 x4 y4

end Gfx
