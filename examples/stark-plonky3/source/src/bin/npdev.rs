//! Developer tool: `npdev check <case-dir>...` proves (with native
//! self-check), verifies and compares the claim with `expected_claim.bin`.
use std::time::Instant;
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(|s| s.as_str()) {
        Some("check") => {
            let selfcheck = std::env::var("NP_SELFCHECK").map(|v| v == "1").unwrap_or(true);
            for dir in &args[1..] {
                let d = std::path::Path::new(dir);
                let req = std::fs::read(d.join("request.bin")).unwrap();
                let wit = std::fs::read(d.join("witness.bin")).unwrap();
                let t = Instant::now();
                match npstark::proof::prove(&req, &wit, selfcheck) {
                    Err(e) => println!("{dir}: PROVE-ERR {e}"),
                    Ok((claim, proof, st)) => {
                        let pt = t.elapsed();
                        let exp = std::fs::read(d.join("expected_claim.bin")).ok();
                        let t2 = Instant::now();
                        let v = npstark::proof::verify(&claim, &proof);
                        println!(
                            "{dir}: claim_ok={} verify={:?} prove={:?} (wit {} ms, trace {} ms, stark {} ms) verify_t={:?} proof={} heights={:?}",
                            exp.as_deref() == Some(&claim[..]),
                            v,
                            pt,
                            st.witness_ms,
                            st.trace_ms,
                            st.prove_ms,
                            t2.elapsed(),
                            proof.len(),
                            st.heights
                        );
                    }
                }
            }
        }
        Some("digest") => {
            let t = Instant::now();
            let d = npstark::proof::air_config_digest();
            println!("{} ({:?})", d.iter().map(|b| format!("{b:02x}")).collect::<String>(), t.elapsed());
        }
        _ => eprintln!("usage: npdev check <dir>... | digest"),
    }
}
