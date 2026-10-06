//! End-to-end tests of the `arena` binary: local packaging/checks and the HTTP
//! client against a tiny in-process mock server.

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpListener;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::process::{Command, Output};
use std::sync::{Arc, Mutex};

const CHL: &str = "chl_0123456789abcdef0123456789abcdef";

fn arena(args: &[&str], env: &[(&str, &str)]) -> Output {
    let cfg = tempfile::tempdir().unwrap();
    let mut c = Command::new(env!("CARGO_BIN_EXE_arena"));
    c.args(args)
        .env_remove("ARENA_URL")
        .env_remove("ARENA_TOKEN")
        .env_remove("ARENA_FIXTURES")
        .env("ARENA_CONFIG", cfg.path().join("none.toml"));
    for (k, v) in env {
        c.env(k, v);
    }
    c.output().unwrap()
}

fn code(o: &Output) -> i32 {
    o.status.code().unwrap_or(-1)
}

fn out(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn write_exec(p: &Path, s: &str) {
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, s).unwrap();
    std::fs::set_permissions(p, std::fs::Permissions::from_mode(0o755)).unwrap();
}

// ---------------------------------------------------------------- local ----

#[test]
fn init_and_skip_build_check() {
    let t = tempfile::tempdir().unwrap();
    let d = t.path().join("my-cand");
    let o = arena(
        &["init-candidate", d.to_str().unwrap(), "--challenge", CHL],
        &[],
    );
    assert_eq!(code(&o), 0, "{o:?}");
    for f in [
        "candidate.toml",
        "README.md",
        "build-recipe/build.sh",
        "formal/Candidate/Certificate.lean",
        "source/Cargo.toml",
        "dependency-locks/Cargo.lock",
    ] {
        assert!(d.join(f).exists(), "{f}");
    }
    let m = std::fs::read_to_string(d.join("candidate.toml")).unwrap();
    assert!(m.contains(CHL) && m.contains("name = \"my-cand\""));
    let o = arena(
        &[
            "check-local",
            d.to_str().unwrap(),
            "--challenge",
            CHL,
            "--skip-build",
        ],
        &[],
    );
    assert_eq!(code(&o), 0, "{}", out(&o));
    assert!(out(&o).contains("LOCAL CHECK — NOT AN OFFICIAL VERDICT"));
    // wrong challenge -> local failure, exit 3
    let other = "chl_ffffffffffffffffffffffffffffffff";
    let o = arena(
        &[
            "check-local",
            d.to_str().unwrap(),
            "--challenge",
            other,
            "--skip-build",
        ],
        &[],
    );
    assert_eq!(code(&o), 3);
    assert!(out(&o).contains("MANIFEST_INVALID"));
    // re-init into non-empty dir refuses
    let o = arena(
        &["init-candidate", d.to_str().unwrap(), "--challenge", CHL],
        &[],
    );
    assert_eq!(code(&o), 2);
}

#[test]
fn template_builds_offline_and_reproducibly() {
    if Command::new("cargo").arg("--version").output().is_err() {
        return;
    }
    let t = tempfile::tempdir().unwrap();
    let d = t.path().join("tpl");
    assert_eq!(
        code(&arena(
            &["init-candidate", d.to_str().unwrap(), "--challenge", CHL],
            &[]
        )),
        0
    );
    let o = arena(
        &[
            "check-local",
            d.to_str().unwrap(),
            "--challenge",
            CHL,
            "--json",
        ],
        &[],
    );
    let v: serde_json::Value = serde_json::from_slice(&o.stdout).unwrap();
    assert_eq!(v["official"], false);
    let build = v["gates"]
        .as_array()
        .unwrap()
        .iter()
        .find(|g| g["gate"] == "BUILD_REPRODUCIBLE")
        .unwrap();
    assert_eq!(build["status"], "PASS", "{v:#}");
    assert_eq!(code(&o), 0);
}

/// A toy shell "prover": claim = sha256(request), proof = sha256(claim || params).
fn toy_candidate(dir: &Path, lenient_verify: bool) {
    std::fs::create_dir_all(dir.join("source")).unwrap();
    std::fs::create_dir_all(dir.join("dependency-locks")).unwrap();
    std::fs::write(dir.join("README.md"), "toy").unwrap();
    std::fs::write(dir.join("dependency-locks/none"), "").unwrap();
    std::fs::write(
        dir.join("candidate.toml"),
        format!(
            r#"schema = "arena-candidate-v1"
name = "toy"
agent = "t"
challenge = "{CHL}"
backend_family = "toy-hash"
security_profile_request = "validity-classical-128"
hardware = {{ gpu = false, min_ram_gb = 1 }}
[build]
recipe = "build-recipe/build.sh"
outputs = ["out/prepare", "out/prove", "out/verify"]
[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"
"#
        ),
    )
    .unwrap();
    write_exec(
        &dir.join("source/prepare"),
        "#!/bin/sh\n# prepare --params P --out D\nset -e\ncp \"$2\" \"$4/params.bin\"\n",
    );
    write_exec(
        &dir.join("source/prove"),
        "#!/bin/sh\nset -e\n# --public D --request R --witness W --claim-out C --proof-out P\n\
         sha256sum < \"$4\" | cut -c1-64 > \"${8}\"\n\
         cat \"$8\" \"$2/params.bin\" | sha256sum | cut -c1-64 > \"${10}\"\n",
    );
    let verify = if lenient_verify {
        "#!/bin/sh\nexit 0\n".to_string()
    } else {
        "#!/bin/sh\n# --public D --claim C --proof P\n\
         cat \"$4\" \"$2/params.bin\" | sha256sum | cut -c1-64 > want || exit 2\n\
         cmp -s want \"$6\" && exit 0 || exit 1\n"
            .to_string()
    };
    write_exec(&dir.join("source/verify"), &verify);
    write_exec(
        &dir.join("build-recipe/build.sh"),
        "#!/bin/sh\nset -e\nmkdir -p out\nfor b in prepare prove verify; do cp source/$b out/$b; chmod 755 out/$b; done\n",
    );
}

fn toy_fixtures(dir: &Path) {
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join("params.bin"), "params-v1").unwrap();
    for (n, req) in [("a", "request-a"), ("b", "request-b")] {
        let c = dir.join("cases").join(n);
        std::fs::create_dir_all(&c).unwrap();
        std::fs::write(c.join("request.bin"), req).unwrap();
        std::fs::write(c.join("witness.bin"), "w").unwrap();
        let o = Command::new("sh")
            .arg("-c")
            .arg(format!("printf %s {req} | sha256sum | cut -c1-64"))
            .output()
            .unwrap();
        std::fs::write(c.join("expected_claim.bin"), o.stdout).unwrap();
    }
}

fn gate<'a>(v: &'a serde_json::Value, g: &str) -> &'a serde_json::Value {
    v["gates"]
        .as_array()
        .unwrap()
        .iter()
        .find(|x| x["gate"] == g)
        .unwrap()
}

#[test]
fn toy_candidate_passes_fixtures() {
    let t = tempfile::tempdir().unwrap();
    let (d, f) = (t.path().join("c"), t.path().join("fx"));
    toy_candidate(&d, false);
    toy_fixtures(&f);
    let o = arena(
        &[
            "check-local",
            d.to_str().unwrap(),
            "--challenge",
            CHL,
            "--fixtures",
            f.to_str().unwrap(),
            "--json",
        ],
        &[],
    );
    let v: serde_json::Value = serde_json::from_slice(&o.stdout).unwrap();
    // No [formal] section -> PKG_WELLFORMED only warns (CERTIFICATE_MISSING).
    assert_eq!(gate(&v, "PKG_WELLFORMED")["status"], "WARN");
    for g in [
        "BUILD_REPRODUCIBLE",
        "CONFORMANCE_DIFFERENTIAL",
        "PROVER_RELIABILITY",
        "ADVERSARIAL_PROOFS",
    ] {
        assert_eq!(gate(&v, g)["status"], "PASS", "{g}: {v:#}");
    }
    assert_eq!(code(&o), 0);
}

#[test]
fn lenient_verifier_is_caught() {
    let t = tempfile::tempdir().unwrap();
    let (d, f) = (t.path().join("c"), t.path().join("fx"));
    toy_candidate(&d, true);
    toy_fixtures(&f);
    let o = arena(
        &[
            "check-local",
            d.to_str().unwrap(),
            "--challenge",
            CHL,
            "--json",
        ],
        &[("ARENA_FIXTURES", f.to_str().unwrap())],
    );
    let v: serde_json::Value = serde_json::from_slice(&o.stdout).unwrap();
    let adv = gate(&v, "ADVERSARIAL_PROOFS");
    assert_eq!(adv["status"], "FAIL");
    assert_eq!(adv["reason_codes"][0], "HOSTILE_PROOF_ACCEPTED");
    assert_eq!(code(&o), 3);
}

#[test]
fn claim_mismatch_is_caught() {
    let t = tempfile::tempdir().unwrap();
    let (d, f) = (t.path().join("c"), t.path().join("fx"));
    toy_candidate(&d, false);
    toy_fixtures(&f);
    std::fs::write(f.join("cases/a/expected_claim.bin"), "nope").unwrap();
    let o = arena(
        &[
            "check-local",
            d.to_str().unwrap(),
            "--challenge",
            CHL,
            "--fixtures",
            f.to_str().unwrap(),
            "--json",
        ],
        &[],
    );
    let v: serde_json::Value = serde_json::from_slice(&o.stdout).unwrap();
    assert_eq!(
        gate(&v, "CONFORMANCE_DIFFERENTIAL")["reason_codes"][0],
        "CLAIM_MISMATCH"
    );
    assert_eq!(code(&o), 3);
}

#[test]
fn nonreproducible_build_is_caught() {
    let t = tempfile::tempdir().unwrap();
    let d = t.path().join("c");
    toy_candidate(&d, false);
    write_exec(
        &d.join("build-recipe/build.sh"),
        "#!/bin/sh\nset -e\nmkdir -p out\nfor b in prepare prove verify; do cp source/$b out/$b; done\ndate +%s%N >> out/prove\n",
    );
    let o = arena(
        &[
            "check-local",
            d.to_str().unwrap(),
            "--challenge",
            CHL,
            "--json",
        ],
        &[],
    );
    let v: serde_json::Value = serde_json::from_slice(&o.stdout).unwrap();
    assert_eq!(
        gate(&v, "BUILD_REPRODUCIBLE")["reason_codes"][0],
        "BUILD_NOT_REPRODUCIBLE"
    );
    assert_eq!(code(&o), 3);
}

#[test]
fn pack_is_deterministic() {
    let t = tempfile::tempdir().unwrap();
    let d = t.path().join("c");
    toy_candidate(&d, false);
    let (a, b) = (t.path().join("a.tar"), t.path().join("b.tar"));
    assert_eq!(
        code(&arena(
            &["pack", d.to_str().unwrap(), "-o", a.to_str().unwrap()],
            &[]
        )),
        0
    );
    // touch a file (new mtime) and re-pack
    std::fs::write(d.join("README.md"), "toy").unwrap();
    assert_eq!(
        code(&arena(
            &["pack", d.to_str().unwrap(), "-o", b.to_str().unwrap()],
            &[]
        )),
        0
    );
    assert_eq!(std::fs::read(&a).unwrap(), std::fs::read(&b).unwrap());
    let (za, zb) = (t.path().join("a.tar.zst"), t.path().join("b.tar.zst"));
    assert_eq!(
        code(&arena(
            &["pack", d.to_str().unwrap(), "-o", za.to_str().unwrap()],
            &[]
        )),
        0
    );
    std::fs::write(d.join("README.md"), "toy").unwrap();
    assert_eq!(
        code(&arena(
            &["pack", d.to_str().unwrap(), "-o", zb.to_str().unwrap()],
            &[]
        )),
        0
    );
    let (za, zb) = (std::fs::read(&za).unwrap(), std::fs::read(&zb).unwrap());
    assert_eq!(za, zb);
    assert_eq!(&za[..4], &[0x28, 0xb5, 0x2f, 0xfd]);
    assert_eq!(
        zstd::decode_all(za.as_slice()).unwrap(),
        std::fs::read(&a).unwrap()
    );
    std::os::unix::fs::symlink("README.md", d.join("link")).unwrap();
    assert_eq!(
        code(&arena(
            &["pack", d.to_str().unwrap(), "-o", b.to_str().unwrap()],
            &[]
        )),
        3
    );
}

// ----------------------------------------------------------------- http ----

#[derive(Clone, Debug)]
struct Req {
    method: String,
    path: String,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}

type Handler = Arc<dyn Fn(&Req) -> (u16, &'static str, String) + Send + Sync>;

struct Mock {
    url: String,
    log: Arc<Mutex<Vec<Req>>>,
}

fn mock(handler: Handler) -> Mock {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let url = format!("http://{}", l.local_addr().unwrap());
    let log = Arc::new(Mutex::new(Vec::new()));
    let log2 = log.clone();
    std::thread::spawn(move || {
        for s in l.incoming() {
            let Ok(mut s) = s else { continue };
            let mut r = BufReader::new(s.try_clone().unwrap());
            let mut line = String::new();
            if r.read_line(&mut line).is_err() || line.is_empty() {
                continue;
            }
            let mut parts = line.split_whitespace();
            let method = parts.next().unwrap_or("").to_string();
            let path = parts.next().unwrap_or("").to_string();
            let mut headers = HashMap::new();
            loop {
                let mut h = String::new();
                r.read_line(&mut h).unwrap();
                let h = h.trim_end();
                if h.is_empty() {
                    break;
                }
                if let Some((k, v)) = h.split_once(':') {
                    headers.insert(k.trim().to_ascii_lowercase(), v.trim().to_string());
                }
            }
            let n: usize = headers
                .get("content-length")
                .and_then(|v| v.parse().ok())
                .unwrap_or(0);
            let mut body = vec![0; n];
            r.read_exact(&mut body).unwrap();
            let req = Req {
                method,
                path,
                headers,
                body,
            };
            log2.lock().unwrap().push(req.clone());
            let (status, ctype, body) = handler(&req);
            let resp = format!(
                "HTTP/1.1 {status} X\r\nContent-Type: {ctype}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
                body.len()
            );
            let _ = s.write_all(resp.as_bytes());
        }
    });
    Mock { url, log }
}

fn view(id: &str, stage: &str, decision: Option<&str>) -> serde_json::Value {
    serde_json::json!({
        "id": id, "challenge_id": CHL, "agent": "a", "candidate_name": "toy",
        "backend_family": "toy-hash", "parent": null, "tier": "formal",
        "package_digest": format!("sha256:{}", "0".repeat(64)),
        "stage": stage, "decision": decision,
        "accepted": decision.map(|d| d == "ADMITTED"),
        "score_milli": null, "change_class": "NO_PARENT",
        "gates": [{
            "gate": "BUILD_REPRODUCIBLE", "mandatory": true, "status": "FAIL",
            "reason_codes": ["BUILD_NOT_REPRODUCIBLE"], "summary": "out/prove differs",
            "evidence": [], "started_at": null, "finished_at": null, "reused_from": null
        }],
        "reason_codes": ["BUILD_NOT_REPRODUCIBLE"], "benchmark": null,
        "evidence_graph": null, "revoked": null,
        "created_at": "2026-10-03T00:00:00Z", "updated_at": "2026-10-03T00:00:00Z",
        "x_extra_server_field": 42
    })
}

#[test]
fn submit_and_watch_flow() {
    let t = tempfile::tempdir().unwrap();
    let d = t.path().join("c");
    toy_candidate(&d, false);
    let polls = Arc::new(Mutex::new(0u32));
    let p2 = polls.clone();
    let m = mock(Arc::new(move |r: &Req| {
        if r.headers.get("authorization").map(|s| s.as_str()) != Some("Bearer tok") {
            return (
                401,
                "application/json",
                r#"{"error":"unauthorized"}"#.into(),
            );
        }
        match (r.method.as_str(), r.path.as_str()) {
            ("POST", "/v1/uploads") => {
                let d = arena_types::Digest::of_bytes(&r.body);
                (
                    200,
                    "application/json",
                    serde_json::json!({"upload_id": "upl_1", "digest": d}).to_string(),
                )
            }
            ("POST", "/v1/submissions") => (
                201,
                "application/json",
                view("sub_1", "RECEIVED", None).to_string(),
            ),
            ("GET", "/v1/submissions/sub_1") => {
                let mut n = p2.lock().unwrap();
                *n += 1;
                if *n < 2 {
                    (
                        200,
                        "application/json",
                        view("sub_1", "VALIDATED", None).to_string(),
                    )
                } else {
                    (
                        200,
                        "application/json",
                        view("sub_1", "DECIDED", Some("REJECTED")).to_string(),
                    )
                }
            }
            ("GET", "/v1/submissions/sub_1/events") => (
                200,
                "text/event-stream",
                "event: stage\nid: 1\ndata: {\"stage\":\"BUILT\"}\n\n".into(),
            ),
            _ => (404, "application/json", "{}".into()),
        }
    }));
    let env = [("ARENA_URL", m.url.as_str()), ("ARENA_TOKEN", "tok")];
    let o = arena(
        &["submit", d.to_str().unwrap(), "--challenge", CHL, "--json"],
        &env,
    );
    assert_eq!(code(&o), 0, "{o:?}");
    let v: serde_json::Value = serde_json::from_slice(&o.stdout).unwrap();
    assert_eq!(v["id"], "sub_1");
    assert_eq!(
        v["x_extra_server_field"], 42,
        "JSON output must be verbatim"
    );
    {
        let log = m.log.lock().unwrap();
        let up = log.iter().find(|r| r.path == "/v1/uploads").unwrap();
        // submit uploads deterministic tar.zst by default
        assert_eq!(
            up.headers.get("content-type").map(|s| s.as_str()),
            Some("application/zstd")
        );
        assert_eq!(&up.body[..4], &[0x28, 0xb5, 0x2f, 0xfd]);
        let sub = log.iter().find(|r| r.path == "/v1/submissions").unwrap();
        let body: serde_json::Value = serde_json::from_slice(&sub.body).unwrap();
        assert_eq!(body["challenge_id"], CHL);
        assert_eq!(
            body["upload_digest"],
            arena_types::Digest::of_bytes(&up.body).to_string()
        );
        assert!(body["idempotency_key"]
            .as_str()
            .unwrap()
            .starts_with("arena-cli-"));
        assert!(body.get("parent").is_none());
    }
    // Same package twice -> same default idempotency key.
    let o = arena(
        &[
            "submit",
            d.to_str().unwrap(),
            "--challenge",
            CHL,
            "--parent",
            "sub_0",
            "--idempotency-key",
            "k1",
        ],
        &env,
    );
    assert_eq!(code(&o), 0);
    {
        let log = m.log.lock().unwrap();
        let subs: Vec<serde_json::Value> = log
            .iter()
            .filter(|r| r.path == "/v1/submissions")
            .map(|r| serde_json::from_slice(&r.body).unwrap())
            .collect();
        assert_eq!(subs[1]["idempotency_key"], "k1");
        assert_eq!(subs[1]["parent"], "sub_0");
    }
    // Watch: decision REJECTED -> exit 10; final JSON is the verbatim view.
    let o = arena(&["status", "sub_1", "--watch", "--json"], &env);
    assert_eq!(code(&o), 10, "{o:?}");
    let v: serde_json::Value = serde_json::from_slice(&o.stdout).unwrap();
    assert_eq!(v["decision"], "REJECTED");
    // Text status renders gates.
    let o = arena(&["status", "sub_1"], &env);
    assert_eq!(code(&o), 0);
    assert!(out(&o).contains("BUILD_NOT_REPRODUCIBLE"));
    // No token -> exit 4 before any network I/O.
    let o = arena(
        &["submit", d.to_str().unwrap(), "--challenge", CHL],
        &[("ARENA_URL", m.url.as_str())],
    );
    assert_eq!(code(&o), 4);
    // Bad token -> 401 -> exit 4.
    let o = arena(
        &["status", "sub_1"],
        &[("ARENA_URL", m.url.as_str()), ("ARENA_TOKEN", "bad")],
    );
    assert_eq!(code(&o), 4);
    // Unknown -> 404 -> exit 7.
    let o = arena(&["status", "sub_404"], &env);
    assert_eq!(code(&o), 7);
}

#[test]
fn read_endpoints() {
    let entry = serde_json::json!({
        "rank": 1, "submission_id": "sub_1", "agent": "a", "candidate_name": "toy",
        "backend_family": "toy", "tier": "formal", "decision": "ADMITTED", "accepted": true,
        "score_milli": 123456, "prove_median_ns": 5000000, "verify_median_ns": 100000,
        "proof_bytes": 1024, "peak_rss_bytes": 1, "hardware_profile": "cpu-32",
        "scope": "transfer-v1", "security_profile": "validity-classical-128",
        "submitted_at": "2026-10-03T00:00:00Z", "revoked": false
    });
    let e2 = entry.clone();
    let m = mock(Arc::new(move |r: &Req| {
        match r.path.as_str() {
        p if p == format!("/v1/leaderboards/{CHL}") => (200, "application/json", serde_json::json!([e2]).to_string()),
        p if p == format!("/v1/challenges/{CHL}") => (200, "application/json", serde_json::json!({"id": CHL, "definition": {"name": "transfer-v1"}}).to_string()),
        "/v1/challenges" => (200, "application/json", serde_json::json!([{"id": CHL, "definition": {"name": "transfer-v1", "tier": "formal", "season": "s1"}}]).to_string()),
        "/v1/submissions/sub_1/report" => (200, "application/json", r#"{"signed":true}"#.into()),
        _ => (404, "text/plain", "nope".into()),
    }
    }));
    let env = [("ARENA_URL", m.url.as_str())];
    let o = arena(&["leaderboard", "--challenge", CHL, "--json"], &env);
    assert_eq!(code(&o), 0);
    let v: serde_json::Value = serde_json::from_slice(&o.stdout).unwrap();
    assert_eq!(v[0], entry);
    let o = arena(&["leaderboard", "--challenge", CHL], &env);
    assert!(out(&o).contains("123.456"), "{}", out(&o));
    let o = arena(&["challenges"], &env);
    assert!(out(&o).contains("transfer-v1"));
    let o = arena(&["challenge", CHL, "--json"], &env);
    let v: serde_json::Value = serde_json::from_slice(&o.stdout).unwrap();
    assert_eq!(v["definition"]["name"], "transfer-v1");
    let t = tempfile::tempdir().unwrap();
    let rp = t.path().join("r.json");
    let o = arena(&["report", "sub_1", "-o", rp.to_str().unwrap()], &env);
    assert_eq!(code(&o), 0);
    assert_eq!(std::fs::read_to_string(&rp).unwrap(), r#"{"signed":true}"#);
    // invalid id -> usage error, no request
    assert_eq!(code(&arena(&["status", "../etc"], &env)), 2);
}

#[test]
fn unreachable_server_is_exit_5() {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let url = format!("http://{}", l.local_addr().unwrap());
    drop(l);
    let o = arena(&["challenges"], &[("ARENA_URL", url.as_str())]);
    assert_eq!(code(&o), 5);
}

#[test]
fn config_file_is_read() {
    let m = mock(Arc::new(|r: &Req| {
        if r.headers.get("authorization").map(|s| s.as_str()) == Some("Bearer filetok") {
            (200, "application/json", "[]".into())
        } else {
            (401, "application/json", "{}".into())
        }
    }));
    let t = tempfile::tempdir().unwrap();
    let cfg = t.path().join("config.toml");
    std::fs::write(&cfg, format!("url = \"{}\"\ntoken = \"filetok\"\n", m.url)).unwrap();
    let mut c = Command::new(env!("CARGO_BIN_EXE_arena"));
    c.args(["challenges", "--json"])
        .env_remove("ARENA_URL")
        .env_remove("ARENA_TOKEN")
        .env("ARENA_CONFIG", &cfg);
    let o = c.output().unwrap();
    assert_eq!(code(&o), 0, "{o:?}");
}

fn sample_challenge() -> arena_types::ChallengeDefinition {
    use arena_types::challenge::*;
    use arena_types::security::*;
    let d = arena_types::Digest::of_bytes(b"x");
    ChallengeDefinition {
        coverage: None,
        schema: "arena-challenge-v1".into(),
        name: "transfer-v1".into(),
        season: "s1".into(),
        tier: Tier::Formal,
        nearcore: NearcorePin {
            repo: "r".into(),
            tag: "2.13.4".into(),
            commit: "c".into(),
        },
        protocol_version: 86,
        chain_id: "mainnet".into(),
        runtime_config_digest: d.clone(),
        semantic_scope: SemanticScope {
            name: "s".into(),
            kind: ScopeKind::Subset,
            granularity: "g".into(),
            restrictions: vec![],
            excludes: vec![],
            formal_spec: FormalSpecRef {
                relation_module: "M".into(),
                relation_decl: "M.R".into(),
                tree_digest: d.clone(),
                lean_toolchain: "t".into(),
            },
            spec_doc_digest: d.clone(),
        },
        claim_encoding: ClaimEncoding {
            format: "near-arena-claim-v1".into(),
            spec_digest: d.clone(),
            max_request_bytes: 1 << 20,
            max_witness_bytes: 1 << 20,
            max_claim_bytes: 1 << 10,
        },
        security_profile: SecurityProfile {
            id: "validity-classical-128".into(),
            privacy: Privacy::ValidityOnly,
            adversary: AdversaryClass::Classical,
            target_bits: 128,
            model: SecurityModel::RandomOracle,
            setup_model: SetupModel::Transparent,
            allowed_assumptions: vec![],
            max_prover_queries_log2: 40,
            max_hash_queries_log2: 64,
            max_aggregation_depth: 4,
            deployment_proofs_log2: 30,
        },
        toolchain_policy: ToolchainPolicy {
            lean_toolchain: "t".into(),
            checker_image: d.clone(),
            axiom_allowlist: vec![],
            allowed_packages: vec![],
            recheckers: vec![],
        },
        required_obligations: vec![],
        not_applicable_gates: vec![],
        hardware_profile: HardwareProfile {
            id: "cpu".into(),
            cpu_model: "x".into(),
            vcpus: 8,
            ram_bytes: 16 << 30,
            gpu: None,
        },
        workload_suite: WorkloadSuite {
            revision: "r1".into(),
            classes: vec![],
            public_fixtures: d.clone(),
            heldout_commitment: d.clone(),
            baseline_submission: None,
            baseline_ns: vec![],
        },
        measurement: MeasurementProcedure {
            warmup_runs: 1,
            measured_runs: 3,
            aggregation: "median".into(),
            outlier_mad_k: 5,
            cold_runs: 1,
            concurrency: 1,
            per_run_timeout_ms: 1000,
            invocation_mode: None,
            calibration: None,
        },
        resource_limits: ResourceLimits {
            max_proof_bytes: 1 << 20,
            max_verify_ms: 10_000,
            max_prove_ms: 60_000,
            max_ram_bytes: 1 << 30,
            max_vram_bytes: 0,
            max_public_artifact_bytes: 1 << 20,
            max_prepare_ms: 60_000,
            max_build_ms: 600_000,
        },
        formal_params: None,
        scoring: None,
        supersedes: None,
        created_at: "2026-10-01T00:00:00Z".into(),
    }
}

#[test]
fn challenge_file_is_authenticated_and_applied() {
    let ch = sample_challenge();
    let id = ch.id().unwrap();
    let t = tempfile::tempdir().unwrap();
    let cf = t.path().join("challenge.json");
    std::fs::write(
        &cf,
        serde_json::to_string(&serde_json::json!({"id": id, "definition": ch})).unwrap(),
    )
    .unwrap();
    let d = t.path().join("c");
    assert_eq!(
        code(&arena(
            &["init-candidate", d.to_str().unwrap(), "--challenge", &id],
            &[]
        )),
        0
    );
    let base = [
        "check-local",
        d.to_str().unwrap(),
        "--challenge-file",
        cf.to_str().unwrap(),
        "--skip-build",
    ];
    let o = arena(&[&base[..], &["--challenge", &id]].concat(), &[]);
    assert_eq!(code(&o), 0, "{}", out(&o));
    // Wrong id for this file -> rejected before anything else.
    let o = arena(&[&base[..], &["--challenge", CHL]].concat(), &[]);
    assert_eq!(code(&o), 3);
    // Profile mismatch -> PROFILE_NOT_ALLOWED.
    let m = std::fs::read_to_string(d.join("candidate.toml")).unwrap();
    std::fs::write(
        d.join("candidate.toml"),
        m.replace("validity-classical-128", "zk-classical-128"),
    )
    .unwrap();
    let o = arena(&[&base[..], &["--challenge", &id]].concat(), &[]);
    assert_eq!(code(&o), 3);
    assert!(out(&o).contains("PROFILE_NOT_ALLOWED"), "{}", out(&o));
}
