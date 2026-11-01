import Lake
open Lake DSL System

package vibecheck

lean_lib Vibecheck
lean_lib App
lean_lib Tools
lean_lib Jsb
lean_lib Envelope
lean_lib JsbExact

/-- SDL3 install prefix; `make` passes `-K sdl=$(brew --prefix sdl3)`. -/
def sdlPrefix : String := (get_config? sdl).getD "/opt/homebrew/opt/sdl3"

target shim.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "shim.c"
  let args := #["-I", (← getLeanIncludeDir).toString, "-I", sdlPrefix ++ "/include", "-O2", "-fPIC"]
  buildO oFile srcJob args #[] "cc"

@[default_target]
lean_exe vibecheck where
  root := `Main
  moreLeancArgs := #["-Dmain=vc_lean_main"]
  moreLinkObjs := #[shim.o]
  moreLinkArgs := #[sdlPrefix ++ "/lib/libSDL3.dylib", "-Wl,-rpath," ++ sdlPrefix ++ "/lib"]

lean_exe simtest where
  root := `Tools.SimTest

lean_exe filtertest where
  root := `Tools.FilterTest

lean_exe jsbresid where
  root := `Tools.JsbResid

lean_exe jsbbench where
  root := `Tools.Bench

/-- C shims for `JsbExact`: libm `sin`/`cos` and Darwin's combined `__sincos_stret`. -/
target jxmath.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "jxmath.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "jxmath.c"
  buildO oFile srcJob #["-O2", "-fPIC", "-fno-builtin"] #[] "cc"

/-- Offline comparison of `JsbExact` against a JSBSim harness dump. -/
lean_exe jsbx where
  root := `Tools.JsbExactResid
  moreLinkObjs := #[jxmath.o]
