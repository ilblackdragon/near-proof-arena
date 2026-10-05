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
use arena_worker::executor::{BuildEnv, FormalEnv, JobExecutor, StageExecutor, WorkerContext};
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
            let helper = HelperCommand {
                exe,
                prefix_args: vec![HELPER_ARG.to_string()],
            };
            let cfg = BwrapConfig::new(helper, work_dir.join("sandbox"));
            Arc::new(BwrapDev::new(cfg).unwrap_or_else(|e| die(e)))
        }
        "firecracker" => {
            let cfg = arena_firecracker::FirecrackerConfig::from_env(&work_dir.join("firecracker"))
                .unwrap_or_else(|e| die(e));
            Arc::new(arena_firecracker::FirecrackerSandbox::new(cfg).unwrap_or_else(|e| die(e)))
        }
        other => die(format!("unknown sandbox backend {other:?}")),
    }
}

fn oracles(dirs: &[PathBuf], near: Option<(PathBuf, PathBuf)>) -> Oracles {
    let mut o = Oracles::builtin();
    if let Some((bin, gens)) = near {
        o = o
            .with_near(bin, &gens)
            .unwrap_or_else(|e| die(format!("NEAR oracle: {e}")));
    }
    for d in dirs {
        match o.add_fixtures_dir(d) {
            Ok(digest) => eprintln!("arena-worker: fixtures {} = {digest}", d.display()),
            Err(e) => die(format!("fixtures dir: {e}")),
        }
    }
    o
}

/// FORMAL_CHECK is enabled by a configs dir; the trusted reference always
/// comes from the frozen trusted-tree store (never a checkout).
fn formal(
    legacy_repo: Option<PathBuf>,
    trusted_trees: Option<PathBuf>,
    configs: Option<PathBuf>,
    images: Option<PathBuf>,
) -> Option<FormalEnv> {
    if legacy_repo.is_some() {
        die("ARENA_FORMAL_REPO is no longer read: the trusted reference is built from the challenge's \
             frozen trusted tree. Set ARENA_TRUSTED_TREES (store published by `arena-admin freeze-trusted`) \
             and ARENA_FORMAL_CONFIGS_DIR instead (docs/TCB.md)");
    }
    let configs_dir = configs?;
    if trusted_trees.is_none() {
        eprintln!("arena-worker: WARNING ARENA_TRUSTED_TREES unset: every FORMAL_CHECK of a configured challenge fails as INFRA_ERROR");
    }
    Some(FormalEnv {
        trusted_trees,
        configs_dir,
        images_dir: images,
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
            let http =
                Arc::new(HttpControl::new(&cfg.server_url, &cfg.token).unwrap_or_else(|e| die(e)));
            let ctx = WorkerContext {
                worker_id: cfg.worker_id.clone(),
                sandbox: sandbox(&cfg.backend, &cfg.work_dir),
                store: http.clone(),
                work_root: cfg.work_dir.join("jobs"),
                build: BuildEnv {
                    mounts: cfg.build_mounts.clone(),
                    path: cfg.build_path.clone(),
                    env: cfg.build_env.clone(),
                    images_dir: cfg.images_dir.clone(),
                    toolchain_image: cfg.toolchain_image.clone(),
                },
                bench_cpus: cfg.bench_cpus.clone(),
                run_cpus: cfg.run_cpus.clone(),
                bench_batch_cap: cfg.bench_batch_cap,
                conformance_samples: cfg.conformance_samples,
                mutators: MutatorRegistry::with_adversarial_lane(),
                oracles: oracles(
                    &cfg.fixtures_dirs,
                    cfg.near_oracle.clone().zip(cfg.workload_generators.clone()),
                ),
                formal: formal(
                    cfg.formal_repo.clone(),
                    cfg.trusted_trees.clone(),
                    cfg.formal_configs_dir.clone(),
                    cfg.lean_checker_images.clone(),
                ),
                npai_verify: cfg.npai_verify.clone(),
                interp_ref: cfg.interp_ref.clone(),
                keep_workdirs: cfg.keep_workdirs,
            };
            let exec = StageExecutor::new(ctx);
            let kinds: Vec<_> = exec
                .kinds()
                .into_iter()
                .filter(|k| cfg.kinds.contains(k))
                .collect();
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
    let (Some(job_path), Some(store)) = (job_path, store) else {
        die("usage: run-job SPEC.json --store DIR [--work DIR]")
    };
    let work = work.unwrap_or_else(|| {
        std::env::temp_dir().join(format!("arena-worker-{}", std::process::id()))
    });
    let spec: JobSpec =
        serde_json::from_slice(&std::fs::read(&job_path).unwrap_or_else(|e| die(e)))
            .unwrap_or_else(|e| die(e));
    let store: Arc<dyn ArtifactStore> = Arc::new(FsStore::new(store).unwrap_or_else(|e| die(e)));
    let fixtures: Vec<PathBuf> = std::env::var("ARENA_FIXTURES_DIRS")
        .map(|v| v.split(',').map(PathBuf::from).collect())
        .unwrap_or_default();
    let ctx = WorkerContext {
        worker_id: "local".into(),
        sandbox: sandbox("bwrap-dev", &work),
        store,
        work_root: work.join("jobs"),
        build: BuildEnv::default(),
        bench_cpus: None,
        run_cpus: None,
        bench_batch_cap: std::env::var("ARENA_DEV_BENCH_BATCH_CAP")
            .ok()
            .and_then(|v| v.parse().ok()),
        conformance_samples: 8,
        mutators: MutatorRegistry::with_adversarial_lane(),
        oracles: oracles(
            &fixtures,
            std::env::var_os("ARENA_NEAR_ORACLE")
                .map(PathBuf::from)
                .zip(std::env::var_os("ARENA_WORKLOAD_GENERATORS").map(PathBuf::from)),
        ),
        formal: formal(
            std::env::var_os("ARENA_FORMAL_REPO").map(PathBuf::from),
            std::env::var_os("ARENA_TRUSTED_TREES").map(PathBuf::from),
            std::env::var_os("ARENA_FORMAL_CONFIGS_DIR").map(PathBuf::from),
            std::env::var_os("ARENA_LEAN_CHECKER_IMAGES").map(PathBuf::from),
        ),
        npai_verify: std::env::var_os("ARENA_NPAI_VERIFY").map(PathBuf::from),
        interp_ref: std::env::var_os("ARENA_INTERP_REF").map(PathBuf::from),
        keep_workdirs: false,
    };
    match StageExecutor::new(ctx).execute(&spec, "local", &AtomicBool::new(false)) {
        Ok(out) => println!("{}", serde_json::to_string_pretty(&out).unwrap()),
        Err(e) => die(e),
    }
}
