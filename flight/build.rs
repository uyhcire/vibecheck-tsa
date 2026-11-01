fn main() {
    if std::env::var_os("CARGO_FEATURE_JSB").is_some() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../.lake/build/lib");
        let dir = dir.canonicalize().expect("build libcityjsb first: `lake build libcityjsb` in the repo root");
        println!("cargo:rustc-link-search=native={}", dir.display());
        println!("cargo:rustc-link-lib=dylib=cityjsb");
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dir.display());
        println!("cargo:rerun-if-changed={}", dir.join("libcityjsb.dylib").display());
    }
}
