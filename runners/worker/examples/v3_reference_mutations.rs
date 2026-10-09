//! Exercise the worker's actual D3 witness-freedom mutators against a built
//! reference verifier. Input directories contain accepted claim.bin/proof.bin.
//! Usage: v3_reference_mutations VERIFY PUBLIC HONEST OUTPUT JOBS
//! Output is aggregate JSON plus per-mutation digests; held-out case names need
//! not be exposed by callers (use digest-named input directories).
use arena_worker::mutators::{v3_freedom_mutants, v3_layout, v3_unread_mutants, V3Pool};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error + Send + Sync>>;
fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn verify(bin: &Path, public: &Path, claim: &Path, proof: &Path) -> Result<i32> {
    let mut child = Command::new(bin)
        .arg("--public")
        .arg(public)
        .arg("--claim")
        .arg(claim)
        .arg("--proof")
        .arg(proof)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()?;
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait()? {
            return status
                .code()
                .ok_or_else(|| "verifier terminated by signal".into());
        }
        if start.elapsed() >= Duration::from_secs(120) {
            child.kill()?;
            child.wait()?;
            return Err("verifier exceeded 120 seconds".into());
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}
struct Case {
    id: String,
    claim: PathBuf,
    proof_path: PathBuf,
    proof: Vec<u8>,
}
fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 5 {
        return Err("usage: v3_reference_mutations VERIFY PUBLIC HONEST OUTPUT JOBS".into());
    }
    let verifier = fs::canonicalize(&args[0])?;
    let public = fs::canonicalize(&args[1])?;
    let honest = fs::canonicalize(&args[2])?;
    let output = PathBuf::from(&args[3]);
    let jobs: usize = args[4].to_str().ok_or("invalid jobs")?.parse()?;
    if !(1..=16).contains(&jobs) {
        return Err("jobs must be 1..16".into());
    }
    fs::create_dir(&output)?;
    let mut dirs = fs::read_dir(&honest)?
        .map(|e| e.map(|e| e.path()))
        .collect::<std::io::Result<Vec<_>>>()?;
    dirs.retain(|p| p.is_dir());
    dirs.sort();
    let mut cases = Vec::new();
    let mut pool = V3Pool::default();
    for dir in dirs {
        let proof_path = dir.join("proof.bin");
        let proof = fs::read(&proof_path)?;
        if v3_layout(&proof).is_none() {
            return Err("input proof is not a D3 witness".into());
        }
        let claim = dir.join("claim.bin");
        let claim_bytes = fs::read(&claim)?;
        let id = digest(&claim_bytes);
        pool.add(&proof);
        cases.push(Case {
            id,
            claim,
            proof_path,
            proof,
        });
    }
    if cases.is_empty() {
        return Err("no honest proofs".into());
    }
    let rows = Mutex::new(BufWriter::new(fs::File::create(
        output.join("mutations.jsonl"),
    )?));
    let next = AtomicUsize::new(0);
    let start = Instant::now();
    let counts = std::thread::scope(|scope| -> Result<BTreeMap<String, usize>> {
        let mut handles = Vec::new();
        for _ in 0..jobs {
            handles.push(scope.spawn(|| -> Result<BTreeMap<String, usize>> {
                let temp = tempfile::tempdir_in(&output)?;
                let mutated = temp.path().join("proof.bin");
                let mut counts = BTreeMap::new();
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(case) = cases.get(index) else { break };
                    if verify(&verifier, &public, &case.claim, &case.proof_path)? != 0 {
                        return Err(format!("honest proof {index} rejected").into());
                    }
                    let mutations = v3_freedom_mutants(&case.proof)
                        .into_iter()
                        .chain(v3_unread_mutants(&case.proof, &pool));
                    for (label, proof) in mutations {
                        if proof == case.proof {
                            return Err("mutator returned unchanged proof".into());
                        }
                        fs::write(&mutated, &proof)?;
                        let code = verify(&verifier, &public, &case.claim, &mutated)?;
                        let row = json!({"case_index":index,"claim_sha256":case.id,"label":label,
                            "base_sha256":digest(&case.proof),"mutant_sha256":digest(&proof),
                            "bytes":proof.len(),"exit_code":code});
                        writeln!(rows.lock().map_err(|_| "output lock poisoned")?, "{row}")?;
                        if code != 1 {
                            fs::write(output.join(format!("failure-{index}-proof.bin")), &proof)?;
                            fs::copy(
                                &case.claim,
                                output.join(format!("failure-{index}-claim.bin")),
                            )?;
                            return Err(format!(
                                "mutation {label} returned {code}, expected reject exit 1"
                            )
                            .into());
                        }
                        *counts.entry(label).or_insert(0) += 1;
                    }
                }
                Ok(counts)
            }));
        }
        let mut total = BTreeMap::new();
        let mut error = None;
        for handle in handles {
            match handle.join().map_err(|_| "mutation worker panicked")? {
                Ok(counts) => {
                    for (label, count) in counts {
                        *total.entry(label).or_insert(0) += count;
                    }
                }
                Err(e) => error = Some(e),
            }
        }
        if let Some(e) = error {
            return Err(e);
        }
        Ok(total)
    })?;
    rows.into_inner()
        .map_err(|_| "output lock poisoned")?
        .flush()?;
    let values: usize = counts
        .iter()
        .filter(|(k, _)| k.starts_with("values/inject-unread."))
        .map(|(_, n)| n)
        .sum();
    let codes = counts.get("codes/inject-unread").copied().unwrap_or(0);
    if values == 0 || codes == 0 {
        return Err("missing values/code unread-injection coverage".into());
    }
    let report = json!({"status":"pass","honest_cases":cases.len(),"mutants":counts.values().sum::<usize>(),
        "counts":counts,"values_inject_unread":values,"codes_inject_unread":codes,
        "verifier_sha256":digest(&fs::read(&verifier)?),
        "mutators_source_sha256":digest(include_bytes!("../src/mutators.rs")),
        "harness_source_sha256":digest(include_bytes!("v3_reference_mutations.rs")),"jobs":jobs,"seconds":start.elapsed().as_secs_f64()});
    fs::write(
        output.join("report.json"),
        serde_json::to_vec_pretty(&report)?,
    )?;
    println!("{report}");
    Ok(())
}
