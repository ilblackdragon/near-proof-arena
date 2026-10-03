//! `run-mutants`: drive a candidate's `verify` executable with every hostile
//! mutant of its honest proofs (what the ADVERSARIAL_PROOFS gate does), and
//! report per-mutator outcomes.
//!
//! ```text
//! run-mutants --verify BIN --public DIR [--seed N] [--jobs N] CASE_DIR...
//! ```
//!
//! Each `CASE_DIR` holds `claim.bin` and `proof.bin` (an honest pair) and
//! optionally `hints.json` (`FormatHints`; otherwise inferred). The next case
//! (cyclically) supplies the foreign claim/proof for binding mutants. A mutant
//! whose bytes and claim equal an honest pair is skipped (not hostile). Exit 0
//! iff no mutant was accepted.

use proof_mutators::{generate_all, FormatHints, MutationCtx};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

struct Job {
    case: String,
    mutator: String,
    label: String,
    kill: String,
    claim: Vec<u8>,
    proof: Vec<u8>,
}

fn main() {
    let mut args = std::env::args().skip(1);
    let (mut verify, mut public, mut seed, mut jobs) = (None, None, 1u64, 8usize);
    let mut cases = Vec::new();
    while let Some(a) = args.next() {
        match a.as_str() {
            "--verify" => verify = args.next().map(PathBuf::from),
            "--public" => public = args.next().map(PathBuf::from),
            "--seed" => seed = args.next().and_then(|s| s.parse().ok()).expect("--seed N"),
            "--jobs" => jobs = args.next().and_then(|s| s.parse().ok()).expect("--jobs N"),
            _ => cases.push(PathBuf::from(a)),
        }
    }
    let (Some(verify), Some(public)) = (verify, public) else {
        eprintln!("usage: run-mutants --verify BIN --public DIR [--seed N] [--jobs N] CASE_DIR...");
        std::process::exit(2);
    };
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
    let pairs: Vec<(String, Vec<u8>, Vec<u8>, FormatHints)> = cases
        .iter()
        .map(|d| {
            let proof = read(d.join("proof.bin"));
            let hints = std::fs::read(d.join("hints.json"))
                .ok()
                .map(|b| serde_json::from_slice(&b).expect("hints.json"))
                .unwrap_or_else(|| FormatHints::infer(&proof));
            (d.file_name().unwrap().to_string_lossy().into_owned(), read(d.join("claim.bin")), proof, hints)
        })
        .collect();
    let honest: std::collections::HashSet<(Vec<u8>, Vec<u8>)> =
        pairs.iter().map(|(_, c, p, _)| (c.clone(), p.clone())).collect();
    let mut work = Vec::new();
    let mut skipped = 0usize;
    for (i, (name, claim, proof, hints)) in pairs.iter().enumerate() {
        let (_, fc, fp, _) = &pairs[(i + 1) % pairs.len()];
        let ctx = MutationCtx {
            hints: hints.clone(),
            foreign_claim: (pairs.len() > 1).then_some(fc.as_slice()),
            foreign_proof: (pairs.len() > 1).then_some(fp.as_slice()),
            claimed_formal_digest: None,
        };
        for m in generate_all(proof, claim, &ctx, seed ^ i as u64) {
            let c = m.claim_override.clone().unwrap_or_else(|| claim.clone());
            if honest.contains(&(c.clone(), m.bytes.clone())) {
                skipped += 1;
                continue;
            }
            work.push(Job {
                case: name.clone(),
                mutator: m.mutator,
                label: m.label,
                kill: format!("{:?}", m.kill),
                claim: c,
                proof: m.bytes,
            });
        }
    }
    let tmp = std::env::temp_dir().join(format!("run-mutants-{}", std::process::id()));
    std::fs::create_dir_all(&tmp).unwrap();
    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<(usize, Option<i32>)>> = Mutex::new(Vec::new());
    std::thread::scope(|s| {
        for t in 0..jobs {
            let (work, next, results, tmp, verify, public) = (&work, &next, &results, &tmp, &verify, &public);
            s.spawn(move || loop {
                let k = next.fetch_add(1, Ordering::Relaxed);
                if k >= work.len() {
                    break;
                }
                let j = &work[k];
                let cp = tmp.join(format!("c{t}"));
                let pp = tmp.join(format!("p{t}"));
                std::fs::write(&cp, &j.claim).unwrap();
                std::fs::write(&pp, &j.proof).unwrap();
                let st = Command::new(verify)
                    .arg("--public")
                    .arg(public)
                    .arg("--claim")
                    .arg(&cp)
                    .arg("--proof")
                    .arg(&pp)
                    .stdout(Stdio::null())
                    .stderr(Stdio::null())
                    .status()
                    .expect("spawn verify");
                results.lock().unwrap().push((k, st.code()));
            });
        }
    });
    let _ = std::fs::remove_dir_all(&tmp);
    let mut per: BTreeMap<String, [usize; 3]> = BTreeMap::new();
    let mut accepted = Vec::new();
    for (k, code) in results.into_inner().unwrap() {
        let j = &work[k];
        let e = per.entry(format!("{} ({})", j.mutator, j.kill)).or_default();
        match code {
            Some(0) => {
                e[2] += 1;
                accepted.push(format!("{}: {} / {}", j.case, j.mutator, j.label));
            }
            Some(1) => e[0] += 1,
            _ => e[1] += 1,
        }
    }
    println!("{:<44} {:>8} {:>8} {:>8}", "mutator (kill)", "reject", "error", "ACCEPT");
    for (k, [r, e, a]) in &per {
        println!("{k:<44} {r:>8} {e:>8} {a:>8}");
    }
    println!("cases {}, mutants run {}, skipped (== honest pair) {skipped}", pairs.len(), work.len());
    for a in &accepted {
        println!("ACCEPTED: {a}");
    }
    std::process::exit(if accepted.is_empty() { 0 } else { 1 });
}
