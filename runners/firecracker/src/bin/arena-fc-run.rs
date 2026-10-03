//! Operator/debug CLI: run one command in a fresh Firecracker microVM and
//! print the `SandboxOutcome` as JSON.
//!
//! ```text
//! arena-fc-run [--mem-mb N] [--scratch-mb N] [--timeout-s N] [--cpus 2,3]
//!              [--pids N] [--ro HOST:GUEST]... [--env K=V]... [--out DIR]
//!              -- argv...
//! ```
//! Uses `$ARENA_FC_DEPS` (default /data/illia/nearproof-deps/firecracker)
//! and `$ARENA_FC_WORK` (default `$ARENA_FC_DEPS/work`).

use arena_firecracker::*;
use std::path::PathBuf;
use std::time::Duration;

fn main() {
    let mut args = std::env::args().skip(1);
    let deps = std::env::var_os("ARENA_FC_DEPS")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/data/illia/nearproof-deps/firecracker"));
    let work = std::env::var_os("ARENA_FC_WORK").map(PathBuf::from).unwrap_or_else(|| deps.join("work"));
    let (mut mem, mut scratch, mut timeout, mut pids) = (512u64, 256u64, 60u64, 256u32);
    let mut cpus = Vec::new();
    let mut ro = Vec::new();
    let mut env = Vec::new();
    let mut out: Option<PathBuf> = None;
    let mut argv = Vec::new();
    while let Some(a) = args.next() {
        let mut val = || args.next().expect("missing value");
        match a.as_str() {
            "--mem-mb" => mem = val().parse().unwrap(),
            "--scratch-mb" => scratch = val().parse().unwrap(),
            "--timeout-s" => timeout = val().parse().unwrap(),
            "--pids" => pids = val().parse().unwrap(),
            "--cpus" => cpus = val().split(',').map(|c| c.parse().unwrap()).collect(),
            "--ro" => {
                let v = val();
                let (h, g) = v.split_once(':').expect("--ro HOST:GUEST");
                ro.push(RoMount { host_path: h.into(), guest_path: g.into() });
            }
            "--env" => {
                let v = val();
                let (k, x) = v.split_once('=').expect("--env K=V");
                env.push((k.to_string(), x.to_string()));
            }
            "--out" => out = Some(val().into()),
            "--" => {
                argv.extend(args.by_ref());
                break;
            }
            _ => {
                argv.push(a);
                argv.extend(args.by_ref());
                break;
            }
        }
    }
    if argv.is_empty() {
        eprintln!("usage: arena-fc-run [options] -- argv...");
        std::process::exit(2);
    }
    let mut cfg = FirecrackerConfig::from_deps_dir(&deps, &work).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(1)
    });
    // experiment hook: ARENA_FC_CAPS=CAP1,CAP2 (used to verify minimality)
    if let Ok(caps) = std::env::var("ARENA_FC_CAPS") {
        cfg.container_caps = caps.split(',').filter(|c| !c.is_empty()).map(str::to_string).collect();
    }
    let sb = FirecrackerSandbox::new(cfg).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(1)
    });
    // without --out, outputs go to a temporary dir removed after printing
    let keep = out.is_some();
    let out_dir = out.unwrap_or_else(|| work.join(format!("out-{}", std::process::id())));
    let spec = SandboxSpec {
        rootfs_digest: sb.rootfs_digest().clone(),
        ro_mounts: ro,
        rw_scratch_mb: scratch,
        argv,
        env,
        cpu_set: cpus,
        mem_bytes: mem << 20,
        pids,
        wall_timeout: Duration::from_secs(timeout),
        network: None,
        out_dir: out_dir.clone(),
    };
    let res = sb.run(&spec);
    if !keep {
        let _ = std::fs::remove_dir_all(&out_dir);
    }
    match res {
        Ok(o) => {
            let mut v = serde_json::to_value(&o).unwrap();
            v["stdout_trunc"] = String::from_utf8_lossy(&o.stdout_trunc).into();
            v["stderr_trunc"] = String::from_utf8_lossy(&o.stderr_trunc).into();
            if keep {
                v["out_dir"] = out_dir.display().to_string().into();
            }
            println!("{}", serde_json::to_string_pretty(&v).unwrap());
        }
        Err(e) => {
            eprintln!("infra error: {e}");
            std::process::exit(1);
        }
    }
}
