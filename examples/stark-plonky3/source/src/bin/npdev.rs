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
        Some("shape") => {
            use p3_air::BaseAir;
            use npstark::config::*;
            let airs = npstark::air::all_airs();
            let degrees: Vec<usize> = npstark::proof::HEIGHT_BOUNDS.iter().map(|b| b.0.max(8)).collect();
            let config = make_config();
            let budgets: Vec<usize> = airs.iter().map(|a| a.lookup_budget()).collect();
            let pd = p3_batch_stark::ProverData::from_airs_and_degrees_with_lookup_budgets(&config, &airs, &degrees, &budgets, LOG_BLOWUP).unwrap();
            let mut tot_main = 0; let mut tot_aux = 0;
            for (i, a) in airs.iter().enumerate() {
                let w = BaseAir::<Val>::width(a);
                let nl = pd.common.lookups[i].len();
                let aux = if nl == 0 { 0 } else { (nl + 1) * EXT_DEGREE };
                let layout = p3_air::AirLayout { preprocessed_width: BaseAir::<Val>::preprocessed_width(a), main_width: w, num_public_values: a.num_pv(), ..Default::default() };
                let lq = p3_batch_stark::symbolic::get_log_num_quotient_chunks::<Val, Challenge, _, _>(a, layout, 1usize << degrees[i], &pd.common.lookups[i], 0, &p3_lookup::LogUpGadget::new());
                println!("{:5} main={:5} lookups={:4} aux_base={:5} log_qchunks={}", a.name(), w, nl, aux, lq);
                tot_main += w; tot_aux += aux;
            }
            println!("total main={tot_main} aux={tot_aux}");
        }
        _ => eprintln!("usage: npdev check <dir>... | digest"),
    }
}
