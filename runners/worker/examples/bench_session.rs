//! Operator tool: run one measurement session (docs/BENCHMARK_SPEC.md) of a
//! built candidate through the worker's real `BENCHMARK` stage on the
//! production Firecracker backend, outside the control plane. Used to
//! measure a challenge's official baseline (reference candidate);
//! `benchmarks/baseline/run_baseline.py` drives it (see its README).
//!
//! The job is exactly what the control plane would lease after BUILD and
//! FORMAL_CHECK: an `ExecJob` whose `BuildOutputs` point at the given built
//! bundle, its frozen public dir and (native-lean route) the judge-built
//! verifier binary. The worker's own NEAR oracle samples the batches (public
//! seeds `derive_seed("workload", class, challenge_id, package_digest)`; the
//! fresh-confirm batch uses `<class>#fresh`), so the inputs are re-derivable
//! by anyone with the oracle at the pinned commit.
//!
//! Around the job: `--calibration-runs` sandboxed runs of a fixed CPU
//! workload before and after (§6.1 stand-in, see `CALIBRATION`), and
//! `/proc/loadavg` samples. Writes one JSON document (`--out`).
//!
//! ```text
//! cargo run -j 8 -p arena-worker --example bench_session -- \
//!   --challenge challenges/chl_….json --package pkg.tar --bundle-dir BUILD \
//!   --public-dir PUB --native-verifier BUILD/out/verify \
//!   --oracle oracle/target/debug/near-arena-oracle \
//!   --generators spec/workloads/near-transfer-receipt-v1 --fixtures oracle/fixtures/public \
//!   --cpus 8-15 --fc-deps DIR --work DIR --out session.json
//! ```

use arena_firecracker::{FirecrackerConfig, FirecrackerSandbox};
use arena_jobs::{BuildOutputs, ExecJob, JobContext, JobSpec};
use arena_sandbox::{ExitStatus, Rootfs, Sandbox, SandboxSpec};
use arena_types::{CandidateManifest, ChallengeDefinition, Digest};
use arena_worker::executor::{BuildEnv, JobExecutor, StageExecutor, WorkerContext};
use arena_worker::mutators::MutatorRegistry;
use arena_worker::oracle::Oracles;
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
    std::fs::read_to_string("/proc/loadavg")
        .unwrap_or_default()
        .trim()
        .to_string()
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

fn calibrate(sb: &dyn Sandbox, cpus: &[u32], n: u32) -> Vec<u64> {
    (0..n)
        .map(|_| {
            let mut s = SandboxSpec::new(vec!["/bin/sh".into(), "-c".into(), CALIBRATION.into()]);
            s.rootfs = Rootfs::BackendDefault;
            s.cwd = sb.layout().scratch.to_string();
            s.cpu_set = Some(cpus.to_vec());
            s.mem_bytes = 512 << 20;
            s.wall_timeout = Duration::from_secs(120);
            let o = sb
                .run(&s)
                .unwrap_or_else(|e| die(format!("calibration: {e}")));
            if o.exit != ExitStatus::Exited(0) {
                die(format!(
                    "calibration exited {:?}: {}",
                    o.exit,
                    String::from_utf8_lossy(&o.stderr_trunc)
                ));
            }
            o.wall_ns
        })
        .collect()
}

/// Put a directory into the store as the deterministic tar the worker
/// fetches; returns (archive digest, TreeDigest).
fn put_tree(store: &FsStore, dir: &Path) -> (Digest, Digest) {
    let tree = arena_archive::tree_from_dir(
        dir,
        &arena_archive::Limits {
            max_expanded_bytes: 4 << 30,
            ..Default::default()
        },
    )
    .unwrap_or_else(|e| die(format!("{}: {e}", dir.display())));
    let tar = arena_archive::pack_tree(dir, &tree, Vec::new()).unwrap();
    (store.put(&tar).unwrap(), tree.digest())
}

fn file_digest(p: &Path) -> Digest {
    Digest::of_bytes(&std::fs::read(p).unwrap_or_else(|e| die(format!("{}: {e}", p.display()))))
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut one: BTreeMap<String, String> = BTreeMap::new();
    let mut it = args.iter();
    while let Some(k) = it.next() {
        let v = it
            .next()
            .unwrap_or_else(|| die(format!("{k} needs a value")))
            .clone();
        one.insert(k.trim_start_matches("--").to_string(), v);
    }
    let get = |k: &str| {
        one.get(k)
            .cloned()
            .unwrap_or_else(|| die(format!("--{k} is required")))
    };
    let chal_bytes = std::fs::read(get("challenge")).unwrap();
    let chal: ChallengeDefinition = serde_json::from_slice(&chal_bytes).unwrap();
    let chal_id = chal.id().unwrap();
    let chal_digest = Digest::of_bytes(&arena_types::canonical_json(&chal).unwrap());
    let cpus = parse_cpus(&one.get("cpus").cloned().unwrap_or_else(|| "8-15".into()));
    let cal_runs: u32 = one
        .get("calibration-runs")
        .map(|s| s.parse().unwrap())
        .unwrap_or(5);
    let deps = PathBuf::from(
        one.get("fc-deps")
            .cloned()
            .unwrap_or_else(|| "/data/illia/nearproof-deps/firecracker".into()),
    );
    let work = PathBuf::from(get("work"));
    std::fs::create_dir_all(&work).unwrap();
    let store = Arc::new(FsStore::new(work.join("store")).unwrap());

    // the candidate as the control plane knows it after BUILD + FORMAL_CHECK
    let package = std::fs::read(get("package")).unwrap();
    let package_digest = store.put(&package).unwrap();
    let bundle_dir = PathBuf::from(get("bundle-dir"));
    let manifest = CandidateManifest::parse(
        &std::fs::read_to_string(bundle_dir.join("candidate.toml")).unwrap(),
    )
    .unwrap_or_else(|e| die(format!("candidate.toml: {e}")));
    let (bundle_archive, bundle_tree) = put_tree(&store, &bundle_dir);
    let public_dir = PathBuf::from(get("public-dir"));
    let (public_archive, public_tree) = put_tree(&store, &public_dir);
    let native_verifier = one.get("native-verifier").map(|p| {
        store
            .put(&std::fs::read(p).unwrap_or_else(|e| die(format!("{p}: {e}"))))
            .unwrap()
    });
    let formal_tree = arena_archive::tree_from_dir(
        &bundle_dir.join(
            manifest
                .formal
                .as_ref()
                .map_or("formal", |f| f.lean_project.as_str()),
        ),
        &arena_archive::Limits::default(),
    )
    .map(|t| t.digest())
    .unwrap_or_else(|_| Digest::of_bytes(b""));
    let build = BuildOutputs {
        prepare: file_digest(&bundle_dir.join(&manifest.entry.prepare)),
        prove: file_digest(&bundle_dir.join(&manifest.entry.prove)),
        verify: file_digest(&bundle_dir.join(&manifest.entry.verify)),
        bundle: bundle_tree.clone(),
        public_artifacts: public_tree.clone(),
        formal_tree,
        certificate_decl: manifest
            .formal
            .as_ref()
            .map(|f| f.certificate.clone())
            .unwrap_or_default(),
        toolchain_image: None,
        build_ns: None,
        bundle_archive: Some(bundle_archive),
        public_archive: Some(public_archive),
        native_verifier: native_verifier.clone(),
        verifier_bytecode: None,
    };
    let job = ExecJob {
        ctx: JobContext {
            submission_id: "sub_baseline".into(),
            run_id: "run_baseline".into(),
            challenge_id: chal_id.clone(),
            challenge_digest: chal_digest,
            tier: chal.tier,
            package_digest: package_digest.clone(),
        },
        challenge: chal.clone(),
        manifest,
        build,
    };

    let mut oracles = Oracles::builtin()
        .with_near(PathBuf::from(get("oracle")), Path::new(&get("generators")))
        .unwrap_or_else(|e| die(format!("near oracle: {e}")));
    let fx = oracles
        .add_fixtures_dir(Path::new(&get("fixtures")))
        .unwrap_or_else(|e| die(e));
    if fx != chal.workload_suite.public_fixtures {
        die(format!(
            "fixtures digest {fx} != challenge public_fixtures {}",
            chal.workload_suite.public_fixtures
        ));
    }
    let fc = Arc::new(
        FirecrackerSandbox::new(
            FirecrackerConfig::from_deps_dir(&deps, &work.join("fc")).unwrap_or_else(|e| die(e)),
        )
        .unwrap_or_else(|e| die(e)),
    );
    let exec = StageExecutor::new(WorkerContext {
        worker_id: "bench-session".into(),
        sandbox: fc.clone(),
        store: store.clone(),
        work_root: work.join("jobs"),
        build: BuildEnv::default(),
        bench_cpus: Some(cpus.clone()),
        bench_batch_cap: None,
        conformance_samples: 0,
        mutators: MutatorRegistry::generic(),
        oracles,
        formal: None,
        npai_verify: None,
        interp_ref: None,
        keep_workdirs: false,
    });

    let mut load = vec![json!({"at": "start", "loadavg": loadavg()})];
    eprintln!("calibration_pre ({cal_runs} runs) …");
    let cal_pre = calibrate(fc.as_ref(), &cpus, cal_runs);
    load.push(json!({"at": "after_calibration_pre", "loadavg": loadavg()}));
    eprintln!("benchmark job …");
    let t0 = std::time::Instant::now();
    let out = exec
        .execute(
            &JobSpec::Benchmark(job.clone()),
            "bench-baseline-1",
            &AtomicBool::new(false),
        )
        .unwrap_or_else(|e| die(format!("benchmark job: {e}")));
    let session_secs = t0.elapsed().as_secs();
    load.push(json!({"at": "after_session", "loadavg": loadavg()}));
    eprintln!("calibration_post …");
    let cal_post = calibrate(fc.as_ref(), &cpus, cal_runs);
    load.push(json!({"at": "after_calibration_post", "loadavg": loadavg()}));

    let session: serde_json::Value = out
        .artifacts
        .iter()
        .find(|a| a.label == "benchmark session")
        .map(|a| serde_json::from_slice(&store.get(&a.digest, 64 << 20).unwrap()).unwrap())
        .unwrap_or(serde_json::Value::Null);
    let doc = json!({
        "schema": "arena-bench-session-v2",
        "challenge_id": chal_id,
        "suite_revision": chal.workload_suite.revision,
        "package_digest": package_digest,
        "sandbox": {"backend": fc.name(), "steps_share_instance": fc.steps_share_instance(),
                    "rootfs": fc.rootfs_digest(), "kernel": fc.kernel_digest()},
        "fc_deps": deps,
        "cpus": cpus,
        "bundle_tree_digest": bundle_tree,
        "public_tree_digest": public_tree,
        "native_verifier": native_verifier,
        "procedure": chal.measurement,
        "sampling": {
            "rule": "worker NearOracle: seed = derive_seed(\"workload\", class_id, challenge_id, package_digest); fresh-confirm uses class_id#fresh",
            "seed_parts": [chal_id, package_digest.to_string()],
        },
        "calibration": {"workload": CALIBRATION, "pre_ns": cal_pre, "post_ns": cal_post},
        "loadavg": load,
        "session_wall_secs": session_secs,
        "job_result": out,
        "session": session,
    });
    std::fs::write(
        get("out"),
        serde_json::to_string_pretty(&doc).unwrap() + "\n",
    )
    .unwrap();
    eprintln!("wrote {}", get("out"));
}
