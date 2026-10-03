//! `prepare --params <approved_params.bin> --out <public_dir>`
//!
//! Run once by the JUDGE (never by you at submit time). Derive public
//! parameters / verifying keys from the approved parameters and write them
//! into `public_dir`. The judge freezes `public_dir` by digest; it is the only
//! state shared between `prove` and `verify` invocations and is mounted
//! read-only afterwards. Must be deterministic.
fn main() {
    let a = candidate::parse_args(&["params", "out"]);
    let params = std::fs::read(&a["params"]).unwrap_or_else(|e| candidate::die(&format!("params: {e}")));
    std::fs::create_dir_all(&a["out"]).unwrap_or_else(|e| candidate::die(&format!("out: {e}")));
    // TODO: derive real public parameters. The template just records the params.
    std::fs::write(a["out"].join("params.bin"), params).unwrap_or_else(|e| candidate::die(&format!("write: {e}")));
}
