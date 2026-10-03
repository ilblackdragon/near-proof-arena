//! NEARPROOF PATCH (zkvm-sp1 candidate): the upstream build script runs `protoc`
//! (not available in the offline build sandbox) and embeds the wall-clock time
//! (BUILD_VERSION, unused by the code). This replacement copies the prost/tonic
//! output generated ONCE with protoc 29.3 from upstream proto/*.proto at
//! sp1-prover-types 6.8.1 (see README.nearproof) into OUT_DIR, and sets a
//! constant BUILD_VERSION. No other file of the crate is changed.
fn main() {
    let out = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap());
    for f in ["cluster.rs", "worker.rs"] {
        let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("generated").join(f);
        println!("cargo:rerun-if-changed={}", src.display());
        std::fs::copy(&src, out.join(f)).expect("copy generated proto code");
    }
    println!("cargo:rustc-env=BUILD_VERSION=nearproof-pinned");
}
