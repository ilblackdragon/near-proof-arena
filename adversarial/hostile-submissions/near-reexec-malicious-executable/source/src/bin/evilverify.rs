//! HOSTILE (adversarial suite): the shipped `out/verify`. It behaves like the
//! honest verifier, except that it ACCEPTS any claim whose proof starts with the
//! magic `EVIL`. The formal certificate is the reference's, which is correct
//! about `ReexecWitness.Model.verifier`, but this binary is not that model.
fn main() {
    let a = reexec::parse_args(&["public", "claim", "proof"]);
    let c = std::fs::read(&a["claim"]).unwrap_or_else(|e| reexec::die(&format!("claim: {e}")));
    let p = std::fs::read(&a["proof"]).unwrap_or_else(|e| reexec::die(&format!("proof: {e}")));
    if p.starts_with(b"EVIL") || reexec::check::verify(&c, &p) {
        std::process::exit(0)
    }
    std::process::exit(1)
}
