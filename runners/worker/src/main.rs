//! `arena-worker` — see the crate docs.
//!
//! ```text
//! arena-worker                     run the daemon (config from env / ARENA_WORKER_CONFIG)
//! arena-worker once                lease and process at most one job, then exit
//! arena-worker run-job JOB.json --store DIR [--work DIR]
//!                                  execute one job locally against a directory
//!                                  artifact store, print JobOutput JSON
//! arena-worker __arena-sandbox-helper (shim|init) CFG   (internal)
//! ```

use arena_sandbox::{BwrapConfig, BwrapDev, HelperCommand, Sandbox};
use arena_worker::client::HttpControlPlane;
use arena_worker::config::{Settings, WorkerConfig};
use arena_worker::daemon::Daemon;
use arena_worker::executor::{BuildEnv, JobExecutor, StageExecutor, WorkerContext};
use arena_worker::jobs::Job;
use arena_worker::mutators::MutatorRegistry;
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
        "firecracker" => die("the firecracker backend is provided by runners/firecracker and is not linked into this build"),
        other => die(format!("unknown sandbox backend {other:?}")),
    }
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
            let http = Arc::new(HttpControlPlane::new(&cfg.server_url, &cfg.token));
            let sb = sandbox(&cfg.backend, &cfg.work_dir);
            let ctx = WorkerContext {
                worker_id: cfg.worker_id.clone(),
                sandbox: sb,
                store: http.clone(),
                work_root: cfg.work_dir.join("jobs"),
                build: BuildEnv { mounts: cfg.build_mounts.clone(), path: cfg.build_path.clone(), env: cfg.build_env.clone(), images_dir: cfg.images_dir.clone() },
                bench_cpus: cfg.bench_cpus.clone(),
                mutators: MutatorRegistry::generic(),
                keep_workdirs: cfg.keep_workdirs,
            };
            let exec = StageExecutor::new(ctx);
            let info = exec.sandbox_info();
            let d = Daemon {
                control: http,
                executor: Arc::new(exec),
                worker_id: cfg.worker_id,
                kinds: cfg.kinds,
                sandbox: info,
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
    let (Some(job_path), Some(store)) = (job_path, store) else { die("usage: run-job JOB.json --store DIR [--work DIR]") };
    let work = work.unwrap_or_else(|| std::env::temp_dir().join(format!("arena-worker-{}", std::process::id())));
    let job: Job = serde_json::from_slice(&std::fs::read(&job_path).unwrap_or_else(|e| die(e))).unwrap_or_else(|e| die(e));
    let store: Arc<dyn ArtifactStore> = Arc::new(FsStore::new(store).unwrap_or_else(|e| die(e)));
    let ctx = WorkerContext {
        worker_id: "local".into(),
        sandbox: sandbox("bwrap-dev", &work),
        store,
        work_root: work.join("jobs"),
        build: BuildEnv::default(),
        bench_cpus: None,
        mutators: MutatorRegistry::generic(),
        keep_workdirs: false,
    };
    match StageExecutor::new(ctx).execute(&job, &AtomicBool::new(false)) {
        Ok(out) => println!("{}", serde_json::to_string_pretty(&out).unwrap()),
        Err(e) => die(e),
    }
}
