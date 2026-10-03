//! `prepare --params <approved_params.bin> --out <public_dir>`
//!
//! Validates the approved parameters and writes `public_dir/public.bin` =
//! format ‖ statement id ‖ sha256(params.bin) ‖ AIR/config digest (the
//! deterministic identity of the constraint system and STARK parameters
//! compiled into this binary; `verify` recomputes it and rejects a mismatch).
fn main() {
    let a = npstark::parse_args(&["params", "out"]);
    let params = std::fs::read(&a["params"]).unwrap_or_else(|e| npstark::die(&format!("params: {e}")));
    if !npstark::proof::params_valid(&params) {
        npstark::die("params: not near-arena-params-v1 for near/pv86/receipt-transfer-batch/v0 (pv 86, mainnet)");
    }
    let digest = npstark::proof::air_config_digest();
    let out = &a["out"];
    std::fs::create_dir_all(out).unwrap_or_else(|e| npstark::die(&format!("out: {e}")));
    std::fs::write(out.join("public.bin"), npstark::proof::public_bin(&params, &digest))
        .unwrap_or_else(|e| npstark::die(&format!("write: {e}")));
}
