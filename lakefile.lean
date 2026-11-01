import Lake
open Lake DSL System

package vibecheck

lean_lib Vibecheck
lean_lib App
lean_lib Tools
lean_lib Jsb
lean_lib Envelope
lean_lib GateSafety
lean_lib CityGate
lean_lib JsbExact
lean_lib VcFilter
lean_lib CityJsb
lean_lib Spec

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

/-- C shims for `JsbExact`'s `Float` instance; every executable using that instance needs `moreLinkObjs := #[jxmath.o]`. -/
target jxmath.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "jxmath.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "jxmath.c"
  buildO oFile srcJob #["-O2", "-fPIC", "-fno-builtin"] #[] "cc"

/-- Offline comparison of `JsbExact` against a JSBSim harness dump. -/
lean_exe jsbx where
  root := `Tools.JsbExactResid
  moreLinkObjs := #[jxmath.o]

target filter_abi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "filter_abi.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "filter_abi.c"
  let hdr ← inputTextFile <| pkg.dir / "c" / "vcfilter.h"
  let rt ← inputTextFile <| pkg.dir / "c" / "lean_runtime.h"
  let args := #["-I", (← getLeanIncludeDir).toString, "-I", (pkg.dir / "c").toString, "-O2", "-fPIC"]
  buildO oFile srcJob args #[] "cc" (do let _ ← hdr.await; let _ ← rt.await; return hdr.getTrace.mix rt.getTrace)

/-- Lean modules of the filter library and the C shim, as static archives. -/
def vcfilterArchives : FetchM (Job (Array FilePath)) := do
  let abi ← filter_abi.o.fetch
  let vc ← (← VcFilter.get).static.fetch
  let env ← (← Envelope.get).static.fetch
  return Job.collectArray #[abi, vc, env]

/-- `libvcfilter.a`: the C ABI and the Lean filter code; link with the Lean runtime libraries. -/
target libvcfilter_static pkg : FilePath := do
  let lib := pkg.buildDir / "lib" / "libvcfilter.a"
  (← vcfilterArchives).mapM fun files => do
    buildFileUnlessUpToDate' lib do
      IO.FS.createDirAll (pkg.buildDir / "lib")
      if (← lib.pathExists) then IO.FS.removeFile lib
      proc {cmd := "libtool", args := #["-static", "-o", lib.toString] ++ files.map (·.toString)}
    return lib

/-- `libvcfilter.dylib`: self-contained (Lean runtime linked in), exports only `vc_*`. -/
target libvcfilter pkg : FilePath := do
  let lib := pkg.buildDir / "lib" / "libvcfilter.dylib"
  let leanLib := (← getLeanLibDir).toString
  let sysLib := ((← getLeanSysroot) / "lib").toString
  (← vcfilterArchives).mapM fun files => do
    buildFileUnlessUpToDate' lib do
      IO.FS.createDirAll (pkg.buildDir / "lib")
      proc {cmd := "cc", args := #["-shared", "-o", lib.toString, "-Wl,-force_load," ++ files[0]!.toString]
        ++ (files.extract 1).map (·.toString) ++ #["-L", leanLib, "-L", sysLib, "-lInit", "-lStd", "-lleanrt",
        "-lgmp", "-luv", "-lc++", "-Wl,-dead_strip", "-Wl,-exported_symbol,_vc_*",
        "-Wl,-install_name,@rpath/libvcfilter.dylib"]}
    return lib

lean_exe citytemplate where
  root := `Tools.CityTemplate

lean_exe cityplanttest where
  root := `Tools.CityPlantTest
  moreLinkObjs := #[jxmath.o]

lean_exe cityimporttest where
  root := `Tools.CityImportTest
  moreLinkObjs := #[jxmath.o]

/-- `CitySafety.passThrough` flown into the hand-made map until an airframe point is in something solid. -/
lean_exe citysafetydemo where
  root := `Tools.CitySafetyDemo
  moreLinkObjs := #[jxmath.o]

lean_exe jsbdrift where
  root := `Tools.JsbDrift
  moreLinkObjs := #[jxmath.o]

lean_exe citygatespot where
  root := `Tools.CityGateSpot
  moreLinkObjs := #[jxmath.o]

target cityjsb_abi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "cityjsb_abi.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "cityjsb_abi.c"
  let hdr ← inputTextFile <| pkg.dir / "c" / "cityjsb.h"
  let ghdr ← inputTextFile <| pkg.dir / "c" / "citygate.h"
  let rt ← inputTextFile <| pkg.dir / "c" / "lean_runtime.h"
  let args := #["-I", (← getLeanIncludeDir).toString, "-I", (pkg.dir / "c").toString, "-O2", "-fPIC"]
  buildO oFile srcJob args #[] "cc"
    (do let _ ← hdr.await; let _ ← ghdr.await; let _ ← rt.await
        return hdr.getTrace.mix (ghdr.getTrace.mix rt.getTrace))

/-- `libcityjsb.dylib`: `JsbExact` as a flight-sim plant and the Lean city gate (`CityGate.Ffi`), Lean runtime linked
in; exports only `cityjsb_*` and `citygate_*`. -/
target libcityjsb pkg : FilePath := do
  let lib := pkg.buildDir / "lib" / (if System.Platform.isOSX then "libcityjsb.dylib" else "libcityjsb.so")
  let leanLib := (← getLeanLibDir).toString
  let sysLib := ((← getLeanSysroot) / "lib").toString
  let abi ← cityjsb_abi.o.fetch
  let jx ← jxmath.o.fetch
  let gate ← (← CityGate.get).static.fetch
  let gsafe ← (← GateSafety.get).static.fetch
  let vcf ← (← VcFilter.get).static.fetch
  let city ← (← CityJsb.get).static.fetch
  let exact ← (← JsbExact.get).static.fetch
  (Job.collectArray #[abi, jx, gate, gsafe, vcf, city, exact]).mapM fun files => do
    buildFileUnlessUpToDate' lib do
      IO.FS.createDirAll (pkg.buildDir / "lib")
      let rest := (files.extract 1).map (·.toString)
      let args := if System.Platform.isOSX then
        #["-shared", "-o", lib.toString, "-Wl,-force_load," ++ files[0]!.toString] ++ rest ++ #["-L", leanLib,
          "-L", sysLib, "-lInit", "-lStd", "-lleanrt", "-lgmp", "-luv", "-lc++", "-Wl,-dead_strip",
          "-Wl,-exported_symbol,_cityjsb_*", "-Wl,-exported_symbol,_citygate_*", "-Wl,-install_name,@rpath/libcityjsb.dylib"]
      else
        #["-shared", "-o", lib.toString, "-Wl,--whole-archive", files[0]!.toString, "-Wl,--no-whole-archive"] ++ rest
          ++ #["-L", leanLib, "-lleanshared", "-Wl,-rpath," ++ leanLib, "-lm", "-lpthread", "-ldl",
          "-Wl,-soname,libcityjsb.so"]
      proc {cmd := "cc", args}
    return lib

/-- Numeric check of the spec bridge's start assumption (`InitChecked cityGate GInit`) and sweep margins. -/
lean_exe specbridgeinit where
  root := `Tools.SpecBridgeInit
  moreLinkObjs := #[jxmath.o]

/-- `jx_*` libm shims as a library, so precompiled modules (`SpecBridgeNative`) can run `JsbExact` in the elaborator. -/
extern_lib jxmath pkg := do
  let o ← jxmath.o.fetch
  let name := nameToStaticLib "jxmath"
  buildStaticLib (pkg.staticLibDir / name) #[o]

/-- `native_decide` proofs that run the plant (`InitChecked` for the spec's starts): imports precompiled. -/
lean_lib SpecBridgeNative where
  precompileModules := true
  precompileImports := true
