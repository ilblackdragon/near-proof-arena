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
        Some("conform") => {
            // Native conformance: in-domain cases -> claim == expected_claim and every AIR
            // constraint + bus satisfied by the generated traces; out-of-domain -> refused.
            use p3_maybe_rayon::prelude::*;
            let mut dirs: Vec<std::path::PathBuf> = vec![];
            for root in &args[1..] {
                for e in std::fs::read_dir(std::path::Path::new(root).join("cases")).unwrap() {
                    dirs.push(e.unwrap().path());
                }
            }
            dirs.sort();
            let res: Vec<(String, String)> = dirs
                .par_iter()
                .map(|d| {
                    let name = d.file_name().unwrap().to_string_lossy().into_owned();
                    let req = std::fs::read(d.join("request.bin")).unwrap();
                    let wit = std::fs::read(d.join("witness.bin")).unwrap();
                    let exp = std::fs::read(d.join("expected_claim.bin")).ok();
                    let r = npstark::witness::build(&req, &wit);
                    let verdict = match (exp, r) {
                        (Some(e), Ok(w)) => {
                            if w.claim_bytes != e {
                                "IN-DOMAIN CLAIM MISMATCH".to_string()
                            } else {
                                let airs = npstark::air::all_airs();
                                let mut tr = npstark::trace::all_traces(&airs, &w);
                                let pvs = npstark::trace::pv_vals(&w.pv);
                                npstark::trace::fill_multiplicities(&airs, &mut tr, &pvs);
                                let rep = npstark::eval::check_all(&airs, &tr, &pvs, 3);
                                if rep.ok() { "in-domain ok".to_string() } else { format!("IN-DOMAIN AIR UNSAT {:?} {:?}", rep.constraint_failures, rep.bus_problems) }
                            }
                        }
                        (Some(_), Err(e)) => format!("IN-DOMAIN REFUSED: {e}"),
                        (None, Ok(_)) => "OUT-OF-DOMAIN ACCEPTED BY PROVER".to_string(),
                        (None, Err(_)) => {
                            // The honest prover refused; now force a witness and check that
                            // the verifier's static checks or the AIR itself reject it.
                            let fam = name.splitn(3, '-').nth(2).unwrap_or("?").to_string();
                            match npstark::witness::build_opts(&req, &wit, false) {
                                Err(e) => format!("out-of-domain [{fam}]: no AIR witness constructible ({})", e.split(':').next().unwrap_or("")),
                                Ok(w) => match npstark::proof::claim_static_check(&w.claim_bytes) {
                                    Err(_) => format!("out-of-domain [{fam}]: rejected by verifier static claim check"),
                                    Ok(()) => {
                                        let airs = npstark::air::all_airs();
                                        let mut tr = npstark::trace::all_traces(&airs, &w);
                                        let pvs = npstark::trace::pv_vals(&w.pv);
                                        npstark::trace::fill_multiplicities(&airs, &mut tr, &pvs);
                                        let rep = npstark::eval::check_all(&airs, &tr, &pvs, 1000);
                                        if rep.ok() {
                                            format!("OUT-OF-DOMAIN [{fam}] FORCED WITNESS SATISFIES AIR")
                                        } else {
                                            let mut tabs: Vec<String> = rep.constraint_failures.iter().map(|(t, _, _)| t.clone()).collect();
                                            tabs.sort();
                                            tabs.dedup();
                                            let buses: Vec<String> = rep.bus_problems.iter().take(1).cloned().collect();
                                            format!("out-of-domain [{fam}]: forced witness rejected by AIR (constraints in {:?}; bus {})", tabs, if buses.is_empty() { "ok".to_string() } else { "imbalance".to_string() })
                                        }
                                    }
                                },
                            }
                        }
                    };
                    (name, verdict)
                })
                .collect();
            let mut counts: std::collections::BTreeMap<String, usize> = Default::default();
            for (n, v) in &res {
                if v.starts_with("IN-DOMAIN") || v.starts_with("OUT-OF-DOMAIN") {
                    println!("{n}: {v}");
                }
                *counts.entry(v.clone()).or_default() += 1;
            }
            for (v, c) in counts {
                println!("{c:6}  {v}");
            }
        }
        Some("breakdown") => {
            // proof size by component
            use npstark::config::MyConfig;
            let proof = std::fs::read(&args[1]).unwrap();
            let body = &proof[4 + npstark::proof::PROOF_FORMAT.len()..];
            let p: p3_batch_stark::BatchProof<MyConfig> = postcard::from_bytes(body).unwrap();
            let sz = |v: &serde_json::Value| -> usize { postcard::to_allocvec(v).unwrap().len() };
            let _ = sz;
            let tree = serde_json::to_value(&p).unwrap();
            fn walk(v: &serde_json::Value, path: String, depth: usize, out: &mut Vec<(String, usize)>) {
                let n = postcard_len(v);
                out.push((path.clone(), n));
                if depth == 0 { return; }
                if let serde_json::Value::Object(o) = v {
                    for (k, x) in o { walk(x, format!("{path}/{k}"), depth - 1, out); }
                }
            }
            fn postcard_len(v: &serde_json::Value) -> usize {
                match v {
                    serde_json::Value::Number(n) => { let x = n.as_u64().unwrap_or(0); if x < 128 {1} else if x < 16384 {2} else if x < 2097152 {3} else if x < 268435456 {4} else {5} }
                    serde_json::Value::Array(a) => 2 + a.iter().map(postcard_len).sum::<usize>(),
                    serde_json::Value::Object(o) => o.values().map(postcard_len).sum(),
                    serde_json::Value::Null => 1,
                    _ => 1,
                }
            }
            let mut out = vec![];
            walk(&tree, String::new(), 3, &mut out);
            println!("total serialized {} (estimate {})", body.len(), postcard_len(&tree));
            for (pth, n) in out { if n > 10000 { println!("{n:9}  {pth}"); } }
            // per-instance opened values
            if let serde_json::Value::Array(insts) = &tree["opened_values"]["instances"] {
                for (i, x) in insts.iter().enumerate() {
                    println!("  instance {i}: {} bytes (trace_local {}, trace_next {}, perm {} , quotient {})", postcard_len(x),
                        postcard_len(&x["base_opened_values"]["trace_local"]), postcard_len(&x["base_opened_values"]["trace_next"]),
                        postcard_len(&x["permutation_local"]) + postcard_len(&x["permutation_next"]), postcard_len(&x["base_opened_values"]["quotient_chunks"]));
                }
            }
            if let serde_json::Value::Array(io) = &tree["opening_proof"]["input_openings"] {
                let q0 = &io[0];
                println!("  input opening per query: {} bytes", postcard_len(q0));
                if let serde_json::Value::Array(ov) = &q0["opened_values"] {
                    for (j, b) in ov.iter().enumerate() { println!("    batch {j}: {} bytes", postcard_len(b)); }
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
        Some("pdtime") => {
            use npstark::config::*;
            let airs = npstark::air::all_airs();
            let config = make_config();
            for (i, a) in airs.iter().enumerate() {
                let t = Instant::now();
                let db = npstark::proof::HEIGHT_BOUNDS[i].0.max(4);
                let _pd = p3_batch_stark::ProverData::from_airs_and_degrees_with_lookup_budgets(&config, std::slice::from_ref(a), &[db], &[a.lookup_budget()], LOG_BLOWUP).unwrap();
                let t1 = t.elapsed();
                let t = Instant::now();
                let l = p3_lookup::Lookups::<Val>::from_air::<Challenge, _>(a);
                let t2 = t.elapsed();
                let layout = p3_air::AirLayout::from_air::<Val>(a);
                let t = Instant::now();
                let (bc, ec) = p3_batch_stark::symbolic::get_symbolic_constraints::<Val, Challenge, _, _>(a, layout, &_pd.common.lookups[0], &p3_lookup::LogUpGadget::new());
                let t3 = t.elapsed();
                println!("{:5} prover_data {:?}  lookups_from_air {:?} ({} lookups) symbolic(packed) {:?} ({} base, {} ext constraints)", a.name(), t1, t2, l.len(), t3, bc.len(), ec.len());
            }
        }
        _ => eprintln!("usage: npdev check <dir>... | digest"),
    }
}
