//! Daemon loop over real HTTP against an in-test fake control plane:
//! lease → fetch by digest → execute → upload → complete / fail.

mod common;

use arena_types::{Digest, GateStatus};
use arena_worker::client::{ClientError, ControlPlane, HttpControlPlane, LeaseRequest};
use arena_worker::daemon::{Daemon, Step};
use arena_worker::executor::{BuildEnv, StageExecutor, WorkerContext};
use arena_worker::jobs::*;
use arena_worker::mutators::MutatorRegistry;
use std::collections::HashMap;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpListener;
use std::sync::{Arc, Mutex};
use std::time::Duration;

#[derive(Default)]
struct State {
    jobs: Vec<Job>,
    artifacts: HashMap<String, Vec<u8>>,
    completed: Vec<serde_json::Value>,
    failed: Vec<serde_json::Value>,
    heartbeats: usize,
    bad_auth: usize,
}

fn serve(state: Arc<Mutex<State>>) -> String {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = format!("http://{}", l.local_addr().unwrap());
    std::thread::spawn(move || {
        for conn in l.incoming() {
            let Ok(mut s) = conn else { continue };
            let state = state.clone();
            std::thread::spawn(move || {
                let mut r = BufReader::new(s.try_clone().unwrap());
                let mut line = String::new();
                r.read_line(&mut line).unwrap();
                let mut parts = line.split_whitespace();
                let (method, path) = (parts.next().unwrap_or("").to_string(), parts.next().unwrap_or("").to_string());
                let mut len = 0usize;
                let mut auth = String::new();
                loop {
                    let mut h = String::new();
                    r.read_line(&mut h).unwrap();
                    if h == "\r\n" || h.is_empty() {
                        break;
                    }
                    let (k, v) = h.split_once(':').unwrap();
                    match k.to_ascii_lowercase().as_str() {
                        "content-length" => len = v.trim().parse().unwrap(),
                        "authorization" => auth = v.trim().to_string(),
                        _ => {}
                    }
                }
                let mut body = vec![0; len];
                r.read_exact(&mut body).unwrap();
                let mut st = state.lock().unwrap();
                let (code, resp): (u16, Vec<u8>) = if auth != "Bearer worker-token" {
                    st.bad_auth += 1;
                    (401, b"no".to_vec())
                } else {
                    match (method.as_str(), path.as_str()) {
                        ("POST", "/internal/v1/jobs/lease") => {
                            let req: LeaseRequest = serde_json::from_slice(&body).unwrap();
                            assert_eq!(req.sandbox.isolation, "bwrap-dev (DEMO-only)");
                            if st.jobs.is_empty() {
                                (204, vec![])
                            } else {
                                (200, serde_json::to_vec(&st.jobs.remove(0)).unwrap())
                            }
                        }
                        ("POST", "/internal/v1/jobs/heartbeat") => {
                            st.heartbeats += 1;
                            (200, br#"{"lease_until":"2099-01-01T00:00:00Z"}"#.to_vec())
                        }
                        ("POST", "/internal/v1/jobs/complete") => {
                            st.completed.push(serde_json::from_slice(&body).unwrap());
                            (200, b"{}".to_vec())
                        }
                        ("POST", "/internal/v1/jobs/fail") => {
                            st.failed.push(serde_json::from_slice(&body).unwrap());
                            (200, b"{}".to_vec())
                        }
                        ("GET", p) if p.starts_with("/internal/v1/artifacts/") => {
                            match st.artifacts.get(&p["/internal/v1/artifacts/".len()..]) {
                                Some(b) => (200, b.clone()),
                                None => (404, b"missing".to_vec()),
                            }
                        }
                        ("PUT", p) if p.starts_with("/internal/v1/artifacts/") => {
                            let d = &p["/internal/v1/artifacts/".len()..];
                            assert_eq!(Digest::of_bytes(&body).as_str(), d, "uploaded bytes must match digest");
                            st.artifacts.insert(d.to_string(), body);
                            (201, vec![])
                        }
                        _ => (404, vec![]),
                    }
                };
                drop(st);
                let _ = write!(s, "HTTP/1.1 {code} X\r\nContent-Length: {}\r\nConnection: close\r\n\r\n", resp.len());
                let _ = s.write_all(&resp);
            });
        }
    });
    addr
}

fn daemon(url: &str, token: &str, tmp: &std::path::Path) -> Daemon {
    let http = Arc::new(HttpControlPlane::new(url, token));
    let helper = arena_sandbox::HelperCommand { exe: env!("CARGO_BIN_EXE_arena-worker").into(), prefix_args: vec![arena_worker::HELPER_ARG.into()] };
    let sb = arena_sandbox::BwrapDev::new(arena_sandbox::BwrapConfig::new(helper, tmp.join("sb"))).unwrap();
    let exec = StageExecutor::new(WorkerContext {
        worker_id: "w1".into(),
        sandbox: Arc::new(sb),
        store: http.clone(),
        work_root: tmp.join("jobs"),
        build: BuildEnv::default(),
        bench_cpus: None,
        mutators: MutatorRegistry::generic(),
        keep_workdirs: false,
    });
    let info = exec.sandbox_info();
    Daemon {
        control: http,
        executor: Arc::new(exec),
        worker_id: "w1".into(),
        kinds: JobKind::ALL.to_vec(),
        sandbox: info,
        poll_interval: Duration::from_millis(10),
        heartbeat_interval: Duration::from_millis(50),
    }
}

#[test]
fn lease_execute_upload_complete() {
    assert_eq!(std::env::var("ARENA_DEV_UNSAFE").as_deref(), Ok("1"));
    let tmp = tempfile::tempdir().unwrap();
    let state = Arc::new(Mutex::new(State::default()));
    let pkg = common::tar_of(&common::package_files());
    let pkg_d = Digest::of_bytes(&pkg);
    {
        let mut st = state.lock().unwrap();
        st.artifacts.insert(pkg_d.to_string(), pkg);
        st.jobs.push(common::job("v1", JobSpec::Validate(ValidateJob { package: pkg_d.clone(), challenge_id: common::CHALLENGE.into() })));
        st.jobs.push(common::job(
            "b1",
            JobSpec::Build(BuildJob { package: pkg_d, toolchain_image: None, limits: common::build_limits(), source_date_epoch: 0 }),
        ));
        // Input that is not in the store: infra failure, retryable.
        st.jobs.push(common::job(
            "v2",
            JobSpec::Validate(ValidateJob { package: Digest::of_bytes(b"nope"), challenge_id: common::CHALLENGE.into() }),
        ));
    }
    let url = serve(state.clone());
    let d = daemon(&url, "worker-token", tmp.path());
    assert_eq!(d.run_once().unwrap(), Step::Completed);
    assert_eq!(d.run_once().unwrap(), Step::Completed);
    assert_eq!(d.run_once().unwrap(), Step::Failed);
    assert_eq!(d.run_once().unwrap(), Step::Idle);

    let st = state.lock().unwrap();
    assert_eq!(st.completed.len(), 2);
    let v: CompleteBody = serde_json::from_value(st.completed[0].clone()).unwrap();
    assert_eq!(v.output.gates[0].status, GateStatus::Pass);
    let manifest = v.output.artifact("manifest").unwrap();
    assert!(st.artifacts.contains_key(manifest.as_str()), "manifest uploaded by digest");
    let b: CompleteBody = serde_json::from_value(st.completed[1].clone()).unwrap();
    assert_eq!(b.output.gates[0].status, GateStatus::Pass, "{}", b.output.gates[0].summary);
    let bundle = b.output.artifact("bundle").unwrap();
    assert!(st.artifacts.contains_key(bundle.as_str()), "bundle uploaded by digest");
    assert_eq!(st.failed.len(), 1);
    assert_eq!(st.failed[0]["retryable"], true);
    assert!(st.failed[0]["error"].as_str().unwrap().contains("not found"));
    assert_eq!(st.bad_auth, 0);
}

#[derive(serde::Deserialize)]
struct CompleteBody {
    output: JobOutput,
}

#[test]
fn wrong_token_is_unauthorized() {
    let tmp = tempfile::tempdir().unwrap();
    let state = Arc::new(Mutex::new(State::default()));
    let url = serve(state.clone());
    let cp = HttpControlPlane::new(&url, "stolen");
    let req = LeaseRequest {
        worker_id: "w".into(),
        kinds: vec![JobKind::Validate],
        sandbox: SandboxInfo { backend: "x".into(), isolation: "x".into(), tier_cap: None },
    };
    assert!(matches!(cp.lease(&req), Err(ClientError::Unauthorized)));
    drop(tmp);
}

#[test]
fn binary_refuses_db_credentials() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_arena-worker"))
        .arg("once")
        .env_clear()
        .env("ARENA_SERVER_URL", "http://127.0.0.1:1")
        .env("ARENA_WORKER_TOKEN", "t")
        .env("DATABASE_URL", "postgres://arena:arena@127.0.0.1:55471/arena")
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("database credentials"));
}
