//! Test-only Rust re-checker: `rxcheck --claim <claim.bin> --proof <proof.bin>`
//! (exit 0 accept, 1 reject). NOT the deployed verifier.
fn main() {
    let a = reexec::parse_args(&["claim", "proof"]);
    let c = std::fs::read(&a["claim"]).unwrap_or_else(|e| reexec::die(&format!("claim: {e}")));
    let p = std::fs::read(&a["proof"]).unwrap_or_else(|e| reexec::die(&format!("proof: {e}")));
    match reexec::check::verify_explain(&c, &p) {
        Ok(()) => std::process::exit(0),
        Err(e) => {
            eprintln!("reject: {e}");
            std::process::exit(1)
        }
    }
}
