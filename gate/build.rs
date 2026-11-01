fn main() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../.lake/build/lib");
    let dir = dir.canonicalize().expect("build libcityjsb first: `lake build libcityjsb` in the repo root");
    // libgate finds libcityjsb next to itself first, then in the build tree.
    println!("cargo:rustc-link-arg=-Wl,-rpath,@loader_path");
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dir.display());
    println!("cargo:rustc-cdylib-link-arg=-Wl,-install_name,@rpath/libgate.dylib");
}
