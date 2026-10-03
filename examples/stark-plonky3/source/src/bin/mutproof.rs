//! Structure-aware adversarial proofs (complements the arena's generic
//! byte-level `proof-mutators`).
//!
//! `mutproof --public DIR [--per-pattern K] [--seed S] CASE_DIR...`
//! (each CASE_DIR holds an honest `claim.bin` + `proof.bin`).
//!
//! 1. Proof-field mutations: the proof is decoded into Plonky3's
//!    `BatchProof`, converted to a serde data tree, and for every distinct
//!    field path pattern (array indices wildcarded: commitments, opened
//!    values per table, quotient chunks, permutation openings, lookup
//!    terminals, degree bits, FRI commit-phase roots, query openings, Merkle
//!    siblings, final polynomial, PoW witnesses, ...) up to K numeric leaves
//!    are perturbed (+1, then re-encoded with the canonical encoder). Every
//!    mutant that still decodes is fed to the verifier.
//! 2. Claim mutations: every byte of the claim is flipped (xor 0x01) with the
//!    honest proof; and each case's proof is checked against every other
//!    case's claim.
//!
//! Exit 0 iff no mutant was accepted. Runs in-process (same code as `verify`).
use npstark::config::MyConfig;
use p3_batch_stark::BatchProof;
use p3_maybe_rayon::prelude::*;
use serde_json::Value;
use std::collections::BTreeMap;

fn leaves(v: &Value, path: &mut Vec<String>, pat: &mut Vec<String>, out: &mut Vec<(String, Vec<String>)>) {
    match v {
        Value::Number(_) => out.push((pat.join("/"), path.clone())),
        Value::Array(a) => {
            for (i, x) in a.iter().enumerate() {
                path.push(i.to_string());
                pat.push("*".into());
                leaves(x, path, pat, out);
                path.pop();
                pat.pop();
            }
        }
        Value::Object(o) => {
            for (k, x) in o {
                path.push(k.clone());
                pat.push(k.clone());
                leaves(x, path, pat, out);
                path.pop();
                pat.pop();
            }
        }
        _ => {}
    }
}

fn get_mut<'a>(v: &'a mut Value, path: &[String]) -> &'a mut Value {
    let mut cur = v;
    for p in path {
        cur = match cur {
            Value::Array(a) => &mut a[p.parse::<usize>().unwrap()],
            Value::Object(o) => o.get_mut(p).unwrap(),
            _ => unreachable!(),
        };
    }
    cur
}

fn frame(body: &[u8]) -> Vec<u8> {
    let mut w = npstark::wire::Writer::with_capacity(body.len() + 32);
    w.bytes(npstark::proof::PROOF_FORMAT).raw(body);
    w.0
}

fn main() {
    let mut args = std::env::args().skip(1);
    let mut k = 2usize;
    let mut seed = 1u64;
    let mut cases = vec![];
    while let Some(a) = args.next() {
        match a.as_str() {
            "--per-pattern" => k = args.next().unwrap().parse().unwrap(),
            "--seed" => seed = args.next().unwrap().parse().unwrap(),
            "--public" => {
                args.next();
            }
            _ => cases.push(std::path::PathBuf::from(a)),
        }
    }
    let pairs: Vec<(String, Vec<u8>, Vec<u8>)> = cases
        .iter()
        .map(|d| {
            (
                d.file_name().unwrap().to_string_lossy().into_owned(),
                std::fs::read(d.join("claim.bin")).unwrap(),
                std::fs::read(d.join("proof.bin")).unwrap(),
            )
        })
        .collect();
    let mut accepted = 0usize;
    let mut table: BTreeMap<String, (usize, usize, usize)> = BTreeMap::new(); // pattern -> (tried, undecodable, rejected)
    for (ci, (name, claim, proof)) in pairs.iter().enumerate() {
        assert!(npstark::proof::verify(claim, proof).is_ok(), "{name}: honest proof rejected");
        let body = &proof[4 + npstark::proof::PROOF_FORMAT.len()..];
        let p: BatchProof<MyConfig> = postcard::from_bytes(body).unwrap();
        let tree = serde_json::to_value(&p).unwrap();
        let mut ls = vec![];
        leaves(&tree, &mut vec![], &mut vec![], &mut ls);
        let mut by: BTreeMap<String, Vec<Vec<String>>> = BTreeMap::new();
        for (pat, path) in ls {
            by.entry(pat).or_default().push(path);
        }
        let mut jobs = vec![];
        let mut rng = seed ^ (ci as u64 * 0x9e3779b97f4a7c15);
        for (pat, paths) in &by {
            for _ in 0..k.min(paths.len()) {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                jobs.push((pat.clone(), paths[(rng % paths.len() as u64) as usize].clone()));
            }
        }
        let results: Vec<(String, u8)> = jobs
            .par_iter()
            .map(|(pat, path)| {
                let mut t = tree.clone();
                let leaf = get_mut(&mut t, path);
                let n = leaf.as_u64().unwrap();
                *leaf = Value::from(n + 1);
                let q: Result<BatchProof<MyConfig>, _> = serde_json::from_value(t);
                let code = match q {
                    Err(_) => 1u8,
                    Ok(q) => {
                        let bytes = frame(&postcard::to_allocvec(&q).unwrap());
                        let r = std::panic::catch_unwind(|| npstark::proof::verify(claim, &bytes));
                        match r {
                            Ok(Ok(())) => 3,
                            _ => 2,
                        }
                    }
                };
                (pat.clone(), code)
            })
            .collect();
        for (pat, code) in results {
            let e = table.entry(pat.clone()).or_default();
            e.0 += 1;
            match code {
                1 => e.1 += 1,
                2 => e.2 += 1,
                _ => {
                    accepted += 1;
                    eprintln!("ACCEPTED mutant: {name} {pat}");
                }
            }
        }
        // claim mutations
        let cm: Vec<bool> = (0..claim.len())
            .into_par_iter()
            .map(|i| {
                let mut c = claim.clone();
                c[i] ^= 1;
                npstark::proof::verify(&c, proof).is_ok()
            })
            .collect();
        let acc = cm.iter().filter(|&&x| x).count();
        accepted += acc;
        println!("{name}: claim byte flips {} rejected, {} accepted", cm.len() - acc, acc);
        for (oi, (oname, oclaim, _)) in pairs.iter().enumerate() {
            if oi != ci && oclaim != claim {
                let ok = npstark::proof::verify(oclaim, proof).is_ok();
                if ok {
                    accepted += 1;
                    eprintln!("ACCEPTED foreign claim {oname} with proof of {name}");
                }
            }
        }
    }
    println!("{:<90} {:>6} {:>8} {:>8}", "proof field pattern", "tried", "undecod", "rejected");
    for (pat, (t, u, r)) in &table {
        println!("{pat:<90} {t:>6} {u:>8} {r:>8}");
    }
    let total: usize = table.values().map(|x| x.0).sum();
    println!("patterns {}, proof-field mutants {}, accepted {}", table.len(), total, accepted);
    std::process::exit(if accepted == 0 { 0 } else { 1 });
}
