//! Operator tool: run one bench-spec-v1 measurement session of a built
//! candidate bundle through the worker's real `BENCHMARK` stage and the
//! production Firecracker backend, outside the control plane. Used to
//! measure the official baseline (reference candidate) of a challenge
//! (`benchmarks/baseline/run_baseline.py` drives it; see that README).
//!
//! What it does, in order:
//!   1. packs `--bundle-dir` (the built package root with `out/…`) and
//!      `--params` into a local content-addressed store;
//!   2. reads every `--class <id>=<dir>` / `--fresh <id>=<dir>` oracle batch
//!      (`<dir>/cases/*/{request,witness,expected_claim}.bin`);
//!   3. calibration_pre: `--calibration-runs` sandboxed runs of a fixed CPU
//!      workload on the benchmark cpus (§6.1 — a stand-in, see `CALIBRATION`);
//!   4. the `BENCHMARK` job (judge-run prepare, cold, warm-up, measured,
//!      fresh-confirm rounds; every proof claim-checked and verified) with
//!      the challenge's `measurement` procedure, limits and request pin;
//!   5. calibration_post;
//!   6. writes one JSON document (`--out`) with the job output, the session
//!      report (every raw run), calibration runs and `/proc/loadavg` samples.
//!
//! Baseline sessions have no baseline yet: `--baseline-ns` defaults to 1 ns
//! per class, so the session's score is meaningless and is not reported as
//! a score; the medians are the product.
//!
//! ```text
//! cargo run -j 8 -p arena-worker --example bench_session -- \
//!   --challenge challenges/chl_….json --bundle-dir BUILD --params params.bin \
//!   --class batch-1=DIR --fresh batch-1=DIR … --cpus 8-15 \
//!   --schedule-seed N --bootstrap-seed N --out session.json
//! ```

use arena_firecracker::{FirecrackerConfig, FirecrackerSandbox};
use arena_sandbox::{ExitStatus, Rootfs, Sandbox, SandboxSpec};
use arena_types::ChallengeDefinition;
use arena_worker::executor::{BuildEnv, JobExecutor, StageExecutor, WorkerContext};
use arena_worker::jobs::*;
use arena_worker::mutators::MutatorRegistry;
use arena_worker::store::{ArtifactStore, FsStore};
use serde_json::json;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;

/// Calibration stand-in (not the governed calibration binary of §6.1, which
/// does not exist yet): sha256 over 256 MiB of zeros, single-threaded,
/// inside the same Firecracker sandbox type and cpu set as the benchmark.
const CALIBRATION: &str = "head -c 268435456 /dev/zero | sha256sum";

fn die(msg: impl std::fmt::Display) -> ! {
    eprintln!("bench_session: {msg}");
    std::process::exit(2)
}

fn loadavg() -> String {
    std::fs::read_to_string("/proc/loadavg").unwrap_or_default().trim().to_string()
}

fn parse_cpus(s: &str) -> Vec<u32> {
    let mut v = vec![];
    for part in s.split(',') {
        match part.split_once('-') {
            Some((a, b)) => v.extend(a.parse::<u32>().unwrap()..=b.parse::<u32>().unwrap()),
            None => v.push(part.parse().unwrap()),
        }
    }
    v
}

fn read_batch(store: &FsStore, class: &str, dir: &Path, tag: &str) -> Vec<OracleCase> {
    let mut names: Vec<PathBuf> = std::fs::read_dir(dir.join("cases"))
        .unwrap_or_else(|e| die(format!("{}: {e}", dir.display())))
        .map(|e| e.unwrap().path())
        .collect();
    names.sort();
    names
        .iter()
        .map(|c| {
            let rd = |f: &str| std::fs::read(c.join(f)).unwrap_or_else(|e| die(format!("{}/{f}: {e}", c.display())));
            OracleCase {
                id: format!("{class}{tag}/{}", c.file_name().unwrap().to_string_lossy()),
                request: store.put(&rd("request.bin")).unwrap(),
                witness: store.put(&rd("witness.bin")).unwrap(),
                expected_claim: store.put(&rd("expected_claim.bin")).unwrap(),
                public: true,
            }
        })
        .collect()
}

fn calibrate(sb: &dyn Sandbox, cpus: &[u32], n: u32) -> Vec<u64> {
    (0..n)
        .map(|_| {
            let mut s = SandboxSpec::new(vec!["/bin/sh".into(), "-c".into(), CALIBRATION.into()]);
            s.rootfs = Rootfs::BackendDefault;
            s.cwd = sb.layout().scratch.to_string();
            s.cpu_set = Some(cpus.to_vec());
            s.mem_bytes = 512 << 20;
            s.wall_timeout = Duration::from_secs(120);
            let o = sb.run(&s).unwrap_or_else(|e| die(format!("calibration: {e}")));
            if o.exit != ExitStatus::Exited(0) {
                die(format!("calibration exited {:?}: {}", o.exit, String::from_utf8_lossy(&o.stderr_trunc)));
            }
            o.wall_ns
        })
        .collect()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut one: BTreeMap<String, String> = BTreeMap::new();
    let mut classes: Vec<(String, PathBuf)> = vec![];
    let mut fresh: BTreeMap<String, PathBuf> = BTreeMap::new();
    let mut baselines: BTreeMap<String, u64> = BTreeMap::new();
    let mut it = args.iter();
    while let Some(k) = it.next() {
        let v = it.next().unwrap_or_else(|| die(format!("{k} needs a value"))).clone();
        let kv = || v.split_once('=').map(|(a, b)| (a.to_string(), b.to_string())).unwrap_or_else(|| die(format!("{k} wants ID=VALUE")));
        match k.as_str() {
            "--class" => classes.push({
                let (a, b) = kv();
                (a, b.into())
            }),
            "--fresh" => {
                let (a, b) = kv();
                fresh.insert(a, b.into());
            }
            "--baseline-ns" => {
                let (a, b) = kv();
                baselines.insert(a, b.parse().unwrap());
            }
            _ => {
                one.insert(k.trim_start_matches("--").to_string(), v);
            }
        }
    }
    let get = |k: &str| one.get(k).cloned().unwrap_or_else(|| die(format!("--{k} is required")));
    let chal: ChallengeDefinition = serde_json::from_slice(&std::fs::read(get("challenge")).unwrap()).unwrap();
    let chal_id = chal.id().unwrap();
    let cpus = parse_cpus(&one.get("cpus").cloned().unwrap_or_else(|| "8-15".into()));
    let cal_runs: u32 = one.get("calibration-runs").map(|s| s.parse().unwrap()).unwrap_or(5);
    let deps = PathBuf::from(one.get("fc-deps").cloned().unwrap_or_else(|| "/data/illia/nearproof-deps/firecracker".into()));
    let work = PathBuf::from(get("work"));
    std::fs::create_dir_all(&work).unwrap();

    let store = Arc::new(FsStore::new(work.join("store")).unwrap());
    let bundle_dir = PathBuf::from(get("bundle-dir"));
    let tree = arena_archive::tree_from_dir(&bundle_dir, &arena_archive::Limits { max_expanded_bytes: 4 << 30, ..Default::default() })
        .unwrap_or_else(|e| die(format!("bundle: {e}")));
    let tar = arena_archive::pack_tree(&bundle_dir, &tree, Vec::new()).unwrap();
    let bundle = store.put(&tar).unwrap();
    let params = store.put(&std::fs::read(get("params")).unwrap()).unwrap();

    let mut bench_classes = vec![];
    for wc in &chal.workload_suite.classes {
        let dir = classes.iter().find(|(c, _)| c == &wc.id).map(|(_, d)| d.clone()).unwrap_or_else(|| die(format!("no --class for {}", wc.id)));
        let batch = read_batch(&store, &wc.id, &dir, "");
        if batch.len() != wc.batch_size as usize {
            die(format!("class {}: {} cases, challenge batch_size {}", wc.id, batch.len(), wc.batch_size));
        }
        let fresh_batch = fresh.get(&wc.id).map(|d| read_batch(&store, &wc.id, d, "#fresh")).unwrap_or_default();
        let baseline_ns = baselines.get(&wc.id).copied().unwrap_or(1);
        bench_classes.push(BenchClass { class_id: wc.id.clone(), weight_ppm: wc.weight_ppm, baseline_ns, batch, fresh_batch });
    }

    let fc = Arc::new(
        FirecrackerSandbox::new(FirecrackerConfig::from_deps_dir(&deps, &work.join("fc")).unwrap_or_else(|e| die(e)))
            .unwrap_or_else(|e| die(e)),
    );
    let exec = StageExecutor::new(WorkerContext {
        worker_id: "bench-session".into(),
        sandbox: fc.clone(),
        store: store.clone(),
        work_root: work.join("jobs"),
        build: BuildEnv::default(),
        bench_cpus: Some(cpus.clone()),
        mutators: MutatorRegistry::generic(),
        keep_workdirs: false,
    });
    let info = exec.sandbox_info();
    let request_pin = RequestPin::from_challenge(&chal);
    let job = BenchmarkJob {
        bundle: bundle.clone(),
        entry: EntryPoints { prepare: "out/prepare".into(), prove: "out/prove".into(), verify: "out/verify".into() },
        params: params.clone(),
        public_artifacts: None,
        classes: bench_classes,
        procedure: chal.measurement.clone(),
        hardware_profile: get("hardware-label"),
        suite_revision: chal.workload_suite.revision.clone(),
        schedule_seed: get("schedule-seed").parse().unwrap(),
        bootstrap_seed: get("bootstrap-seed").parse().unwrap(),
        bootstrap_iterations: 10_000,
        limits: RunLimits::from_challenge(&chal),
        request_pin: request_pin.clone(),
    };

    let mut load = vec![json!({"at": "start", "loadavg": loadavg()})];
    eprintln!("calibration_pre ({cal_runs} runs) …");
    let cal_pre = calibrate(fc.as_ref(), &cpus, cal_runs);
    load.push(json!({"at": "after_calibration_pre", "loadavg": loadavg()}));
    eprintln!("benchmark job …");
    let t0 = std::time::Instant::now();
    let out = exec
        .execute(&Job { id: "bench".into(), submission_id: "baseline".into(), attempt: 1, lease_until: "2099-01-01T00:00:00Z".into(), spec: JobSpec::Benchmark(job.clone()) }, &AtomicBool::new(false))
        .unwrap_or_else(|e| die(format!("benchmark job: {e}")));
    let session_secs = t0.elapsed().as_secs();
    load.push(json!({"at": "after_session", "loadavg": loadavg()}));
    eprintln!("calibration_post …");
    let cal_post = calibrate(fc.as_ref(), &cpus, cal_runs);
    load.push(json!({"at": "after_calibration_post", "loadavg": loadavg()}));

    let session: serde_json::Value = out
        .artifact("benchmark_session")
        .map(|d| serde_json::from_slice(&store.get(d, 64 << 20).unwrap()).unwrap())
        .unwrap_or(serde_json::Value::Null);
    let doc = json!({
        "schema": "arena-bench-session-v1",
        "challenge_id": chal_id,
        "suite_revision": chal.workload_suite.revision,
        "hardware_label": get("hardware-label"),
        "sandbox": info,
        "cpus": cpus,
        "bundle_tar_digest": bundle,
        "bundle_tree_digest": tree.digest(),
        "params_digest": params,
        "request_pin": request_pin,
        "procedure": chal.measurement,
        "schedule_seed": job.schedule_seed,
        "bootstrap_seed": job.bootstrap_seed,
        "classes": job.classes.iter().map(|c| json!({
            "class_id": c.class_id, "weight_ppm": c.weight_ppm, "baseline_ns_used": c.baseline_ns,
            "batch": c.batch, "fresh_batch": c.fresh_batch,
        })).collect::<Vec<_>>(),
        "calibration": {"workload": CALIBRATION, "pre_ns": cal_pre, "post_ns": cal_post},
        "loadavg": load,
        "session_wall_secs": session_secs,
        "job_output": out,
        "session": session,
    });
    std::fs::write(get("out"), serde_json::to_string_pretty(&doc).unwrap() + "\n").unwrap();
    eprintln!("wrote {}", get("out"));
}
