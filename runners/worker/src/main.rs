//! `arena-worker` — see the crate docs.
//!
//! ```text
//! arena-worker                     run the daemon (config from env / ARENA_WORKER_CONFIG)
//! arena-worker once                lease and process at most one job, then exit
//! arena-worker run-job SPEC.json --store DIR [--work DIR]
//!                                  execute one arena_jobs::JobSpec locally against a
//!                                  directory artifact store, print the JobResult JSON
//! arena-worker __arena-sandbox-helper (shim|init) CFG   (internal)
//! ```
//!
//! Backends (`ARENA_SANDBOX_BACKEND`): `bwrap-dev` (default; DEMO-only, needs
//! `ARENA_DEV_UNSAFE=1`) or `firecracker` (production microVMs; assets from
//! `deploy/images/*`, `$ARENA_FC_DEPS`). Build and formal-check jobs
//! currently need bwrap-dev (copy-in / read-write dirs).

use arena_sandbox::{BwrapConfig, BwrapDev, HelperCommand, Sandbox};
use arena_worker::config::{Settings, WorkerConfig};
use arena_worker::control::HttpControl;
use arena_worker::daemon::Daemon;
use arena_worker::executor::{BuildEnv, FormalConfig, JobExecutor, StageExecutor, WorkerContext};
use arena_worker::jobs::JobSpec;
use arena_worker::mutators::MutatorRegistry;
use arena_worker::oracle::Oracles;
use arena_worker::store::{ArtifactStore, FsStore};
use arena_worker::HELPER_ARG;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

fn die(msg: impl std::fmt::Display) -> ! {
    eprintln!("arena-worker: {msg}");
    std::process::exit(2)
}

fn sandbox(backend: &str, work_dir: &Path) -> Arc<dyn Sandbox> {
    match backend {
        "bwrap-dev" => {
            let exe = std::env::current_exe().unwrap_or_else(|e| die(e));
            let helper = HelperCommand { exe, prefix_args: vec![HELPER_ARG.to_string()] };
            let cfg = BwrapConfig::new(helper, work_dir.join("sandbox"));
            Arc::new(BwrapDev::new(cfg).unwrap_or_else(|e| die(e)))
        }
        "firecracker" => {
            let cfg = arena_firecracker::FirecrackerConfig::from_env(&work_dir.join("firecracker")).unwrap_or_else(|e| die(e));
            Arc::new(arena_firecracker::FirecrackerSandbox::new(cfg).unwrap_or_else(|e| die(e)))
        }
        other => die(format!("unknown sandbox backend {other:?}")),
    }
}

fn oracles(dirs: &[PathBuf]) -> Oracles {
    let mut o = Oracles::builtin();
    for d in dirs {
        match o.add_fixtures_dir(d) {
            Ok(digest) => eprintln!("arena-worker: fixtures {} = {digest}", d.display()),
            Err(e) => die(format!("fixtures dir: {e}")),
        }
    }
    o
}

fn formal(p: &Option<PathBuf>) -> Option<FormalConfig> {
    p.as_ref().map(|p| {
        let b = std::fs::read(p).unwrap_or_else(|e| die(format!("{}: {e}", p.display())));
        serde_json::from_slice(&b).unwrap_or_else(|e| die(format!("{}: {e}", p.display())))
    })
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some(HELPER_ARG) {
        std::process::exit(arena_sandbox::helper::helper_main(&args[2..]));
    }
    match args.get(1).map(String::as_str) {
        Some("run-job") => run_job_local(&args[2..]),
        None | Some("once") => {
            let settings = Settings::from_process().unwrap_or_else(|e| die(e));
            let cfg = WorkerConfig::load(&settings).unwrap_or_else(|e| die(e));
            let http = Arc::new(HttpControl::new(&cfg.server_url, &cfg.token).unwrap_or_else(|e| die(e)));
            let ctx = WorkerContext {
                worker_id: cfg.worker_id.clone(),
                sandbox: sandbox(&cfg.backend, &cfg.work_dir),
                store: http.clone(),
                work_root: cfg.work_dir.join("jobs"),
                build: BuildEnv { mounts: cfg.build_mounts.clone(), path: cfg.build_path.clone(), env: cfg.build_env.clone(), images_dir: cfg.images_dir.clone(), toolchain_image: cfg.toolchain_image.clone() },
                bench_cpus: cfg.bench_cpus.clone(),
                bench_batch_cap: cfg.bench_batch_cap,
                conformance_samples: cfg.conformance_samples,
                mutators: MutatorRegistry::with_adversarial_lane(),
                oracles: oracles(&cfg.fixtures_dirs),
                formal: formal(&cfg.formal_config),
                keep_workdirs: cfg.keep_workdirs,
            };
            let exec = StageExecutor::new(ctx);
            let kinds: Vec<_> = exec.kinds().into_iter().filter(|k| cfg.kinds.contains(k)).collect();
            eprintln!(
                "arena-worker {}: backend {} (tier cap {:?}), kinds {:?}",
                cfg.worker_id,
                cfg.backend,
                exec.tier_cap(),
                kinds.iter().map(|k| k.as_str()).collect::<Vec<_>>()
            );
            let d = Daemon {
                control: http,
                executor: Arc::new(exec),
                kinds,
                lease_seconds: cfg.lease_seconds,
                poll_interval: cfg.poll_interval,
                heartbeat_interval: cfg.heartbeat_interval,
            };
            if args.get(1).is_some() {
                match d.run_once() {
                    Ok(s) => eprintln!("arena-worker: {s:?}"),
                    Err(e) => die(e),
                }
            } else {
                d.run_forever(&AtomicBool::new(false));
            }
        }
        Some(other) => die(format!("unknown command {other:?}")),
    }
}

fn run_job_local(args: &[String]) {
    let mut job_path = None;
    let mut store = None;
    let mut work = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--store" => store = it.next().map(PathBuf::from),
            "--work" => work = it.next().map(PathBuf::from),
            p => job_path = Some(PathBuf::from(p)),
        }
    }
    let (Some(job_path), Some(store)) = (job_path, store) else { die("usage: run-job SPEC.json --store DIR [--work DIR]") };
    let work = work.unwrap_or_else(|| std::env::temp_dir().join(format!("arena-worker-{}", std::process::id())));
    let spec: JobSpec = serde_json::from_slice(&std::fs::read(&job_path).unwrap_or_else(|e| die(e))).unwrap_or_else(|e| die(e));
    let store: Arc<dyn ArtifactStore> = Arc::new(FsStore::new(store).unwrap_or_else(|e| die(e)));
    let fixtures: Vec<PathBuf> = std::env::var("ARENA_FIXTURES_DIRS").map(|v| v.split(',').map(PathBuf::from).collect()).unwrap_or_default();
    let ctx = WorkerContext {
        worker_id: "local".into(),
        sandbox: sandbox("bwrap-dev", &work),
        store,
        work_root: work.join("jobs"),
        build: BuildEnv::default(),
        bench_cpus: None,
        bench_batch_cap: std::env::var("ARENA_DEV_BENCH_BATCH_CAP").ok().and_then(|v| v.parse().ok()),
        conformance_samples: 8,
        mutators: MutatorRegistry::with_adversarial_lane(),
        oracles: oracles(&fixtures),
        formal: formal(&std::env::var_os("ARENA_FORMAL_CONFIG").map(PathBuf::from)),
        keep_workdirs: false,
    };
    match StageExecutor::new(ctx).execute(&spec, "local", &AtomicBool::new(false)) {
        Ok(out) => println!("{}", serde_json::to_string_pretty(&out).unwrap()),
        Err(e) => die(e),
    }
}
