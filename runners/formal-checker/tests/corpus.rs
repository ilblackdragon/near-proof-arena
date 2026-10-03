//! Runs every case under `tests/corpus/` through the real pipeline
//! (bwrap-dev sandbox, real Lean toolchain, leanchecker, lean4export, nanoda,
//! arena-audit) and compares against `expect.json`.
//!
//! Requirements: `scripts/setup-tools.sh` has been run and `ARENA_DEV_UNSAFE=1`.
//! Without them the test only checks that the dev runner refuses to start and
//! prints SKIP. Filter with `FC_CASE=<substring>`; parallelism `FC_JOBS` (default 6).

use arena_formal_checker::*;
use arena_types::{GateStatus, ObligationId, ReasonCode};
use serde_json::Value;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn gate_name(g: ObligationId) -> String {
    serde_json::to_value(g).unwrap().as_str().unwrap().to_string()
}
fn code_name(c: ReasonCode) -> String {
    serde_json::to_value(c).unwrap().as_str().unwrap().to_string()
}
fn status_name(s: GateStatus) -> String {
    serde_json::to_value(s).unwrap().as_str().unwrap().to_string()
}

fn expected_builder() -> TemplateExpected {
    serde_json::from_slice(&std::fs::read(crate_dir().join("tests/fixtures/expected.json")).unwrap()).unwrap()
}

fn policy_for(expect: &Value) -> Policy {
    let mut p = Policy { allowed_requires: vec!["arena-standin".into()], ..Policy::default() };
    if expect.get("conjuncts").and_then(Value::as_bool) == Some(true) {
        p.conjunct_gates = Some(vec![
            ObligationId::FormalSemanticSoundness,
            ObligationId::FormalSemanticCompleteness,
            ObligationId::FormalCryptoSoundness,
            ObligationId::FormalImplConnection,
        ]);
    }
    p
}

fn check_case(name: &str, expect: &Value, rep: &FormalCheckReport, scratch: &Path) -> Vec<String> {
    let mut errs = Vec::new();
    let gates: std::collections::BTreeMap<String, (String, Vec<String>)> = rep
        .gates
        .iter()
        .map(|g| (gate_name(g.gate), (status_name(g.status), g.reason_codes.iter().map(|c| code_name(*c)).collect())))
        .collect();
    if let Some(all) = expect.get("all") {
        let st = all["status"].as_str().unwrap();
        for (g, (s, _)) in &gates {
            if s != st {
                errs.push(format!("{name}: gate {g} is {s}, expected {st}"));
            }
        }
        let union: std::collections::BTreeSet<&String> = gates.values().flat_map(|(_, c)| c.iter()).collect();
        for c in all["codes"].as_array().unwrap() {
            let c = c.as_str().unwrap().to_string();
            if !union.contains(&c) {
                errs.push(format!("{name}: expected reason code {c}, got {union:?}"));
            }
        }
    }
    if let Some(per) = expect.get("gates").and_then(Value::as_object) {
        for (g, e) in per {
            let Some((s, codes)) = gates.get(g) else {
                errs.push(format!("{name}: gate {g} missing"));
                continue;
            };
            if e["status"].as_str() != Some(s.as_str()) {
                errs.push(format!("{name}: gate {g} is {s}, expected {}", e["status"]));
            }
            for c in e.get("codes").and_then(Value::as_array).into_iter().flatten() {
                if !codes.iter().any(|x| Some(x.as_str()) == c.as_str()) {
                    errs.push(format!("{name}: gate {g} missing code {c} (has {codes:?})"));
                }
            }
        }
    }
    if expect.get("check_no_fake_pass").and_then(Value::as_bool) == Some(true) {
        for p in ["report.json", "PASS", "work/report.json"] {
            if scratch.join(p).exists() {
                errs.push(format!("{name}: candidate managed to write {p} on the host"));
            }
        }
        if rep.gates.iter().any(|g| g.status == GateStatus::Pass) {
            errs.push(format!("{name}: fake PASS output influenced a gate"));
        }
    }
    errs
}

#[test]
fn corpus() {
    if std::env::var("ARENA_DEV_UNSAFE").as_deref() != Ok("1") {
        assert!(dev_runner().is_err(), "dev runner must refuse without ARENA_DEV_UNSAFE=1");
        eprintln!("SKIP corpus: set ARENA_DEV_UNSAFE=1 to run the formal checker corpus");
        return;
    }
    let tools = match toolchain::ToolPaths::discover() {
        Ok(t) => t,
        Err(e) => {
            eprintln!("SKIP corpus: {e}");
            return;
        }
    };
    let filter = std::env::var("FC_CASE").ok();
    let jobs: usize = std::env::var("FC_JOBS").ok().and_then(|s| s.parse().ok()).unwrap_or(6);
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("fc-corpus");
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).unwrap();
    let cache = root.join("ref-cache");
    let checker = Arc::new(FormalChecker::new(tools, Box::new(dev_runner().unwrap())));
    let expected = Arc::new(expected_builder());
    let trusted = vec![TrustedPackage { name: "arena-standin".into(), src_root: crate_dir().join("tests/fixtures/standin"), include: None }];

    // Warm the reference cache once (serially) so cases run in parallel.
    let t0 = Instant::now();
    {
        let req = CheckRequest {
            formal_dir: crate_dir().join("tests/corpus/pos_basic/formal"),
            certificate: "Candidate.certificate".into(),
            trusted: trusted.clone(),
            expected: &*expected,
            challenge_digest: None,
            policy: policy_for(&Value::Null),
            limits: Limits::default(),
            work_dir: root.join("warmup"),
            cache_dir: cache.clone(),
        };
        let _ = checker.check(&req);
    }
    eprintln!("reference build + warmup: {:?}", t0.elapsed());
    let ref_dir = std::fs::read_dir(&cache).unwrap().next().unwrap().unwrap().path().join("out");
    let ref_digest_before = digest::tree_digest(&ref_dir).unwrap();

    let mut cases: Vec<PathBuf> = std::fs::read_dir(crate_dir().join("tests/corpus"))
        .unwrap()
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.join("expect.json").is_file())
        .filter(|p| filter.as_ref().is_none_or(|f| p.file_name().unwrap().to_str().unwrap().contains(f.as_str())))
        .collect();
    cases.sort();
    let queue = Arc::new(Mutex::new(cases));
    let results = Arc::new(Mutex::new(Vec::new()));
    let mut handles = Vec::new();
    for _ in 0..jobs {
        let (queue, results, checker, expected, trusted, root, cache) =
            (queue.clone(), results.clone(), checker.clone(), expected.clone(), trusted.clone(), root.clone(), cache.clone());
        handles.push(std::thread::spawn(move || loop {
            let Some(case) = queue.lock().unwrap().pop() else { break };
            let name = case.file_name().unwrap().to_str().unwrap().to_string();
            let expect: Value = serde_json::from_slice(&std::fs::read(case.join("expect.json")).unwrap()).unwrap();
            let mut limits = Limits::default();
            if let Some(s) = expect.get("module_timeout_s").and_then(Value::as_u64) {
                limits.module_timeout = Duration::from_secs(s);
            }
            let scratch = root.join(&name);
            let req = CheckRequest {
                formal_dir: case.join("formal"),
                certificate: "Candidate.certificate".into(),
                trusted: trusted.clone(),
                expected: &*expected,
                challenge_digest: None,
                policy: policy_for(&expect),
                limits,
                work_dir: scratch.join("work"),
                cache_dir: cache.clone(),
            };
            let t = Instant::now();
            let rep = checker.check(&req);
            let wall = t.elapsed();
            let errs = check_case(&name, &expect, &rep, &scratch);
            let _ = std::fs::write(scratch.join("report.out.json"), serde_json::to_string_pretty(&rep).unwrap());
            results.lock().unwrap().push((name, wall, rep, errs));
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    let mut results = std::mem::take(&mut *results.lock().unwrap());
    results.sort_by(|a, b| a.0.cmp(&b.0));
    let mut failures = Vec::new();
    eprintln!("\n{:<30} {:>8}  {:<8} {:<60} rechecks", "case", "wall", "result", "codes");
    for (name, wall, rep, errs) in &results {
        let mut codes: Vec<String> = rep.gates.iter().flat_map(|g| g.reason_codes.iter().map(|c| code_name(*c))).collect();
        codes.sort();
        codes.dedup();
        let statuses: std::collections::BTreeSet<String> = rep.gates.iter().map(|g| status_name(g.status)).collect();
        let rc: Vec<String> = rep.rechecks.iter().filter(|r| r.ran).map(|r| format!("{}={}", r.id, r.verdict)).collect();
        eprintln!(
            "{:<30} {:>7.1}s  {:<8} {:<60} {}",
            name,
            wall.as_secs_f64(),
            statuses.into_iter().collect::<Vec<_>>().join("/"),
            codes.join(","),
            rc.join(" ")
        );
        if !errs.is_empty() {
            for f in &rep.findings {
                eprintln!("    finding: {:?} {:?} {}", f.code, f.severity, f.detail.lines().next().unwrap_or(""));
            }
        }
        failures.extend(errs.iter().cloned());
    }
    let ref_digest_after = digest::tree_digest(&ref_dir).unwrap();
    if ref_digest_before != ref_digest_after {
        failures.push("judge reference .olean tree was modified during candidate runs".into());
    }
    if !failures.is_empty() {
        panic!("corpus failures:\n{}", failures.join("\n"));
    }
}

fn dev_runner() -> Result<SandboxRunner, arena_formal_checker::sandbox::InfraError> {
    let helper = arena_sandbox::HelperCommand {
        exe: env!("CARGO_BIN_EXE_formal-check").into(),
        prefix_args: vec![arena_formal_checker::HELPER_ARG.into()],
    };
    let work = std::env::temp_dir().join(format!("fc-sandbox-{}", std::process::id()));
    SandboxRunner::bwrap_dev(helper, work)
}
