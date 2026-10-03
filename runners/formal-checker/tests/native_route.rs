//! `native-lean` verifier route against the in-repo formal-core (`ArenaCore`
//! + `Toy.Spec` trusted). The candidate supplies a Lean verifier model
//! (`Candidate.Model.verify : ArenaCore.OracleVerifier`); the judge builds the
//! native `verify` from it, pins the build digest in the statement
//! (`.nativeTrusted <digest> <toolchain> Candidate.Model.verify`), and checks
//! the certificate against the statement instantiated at the model.
//!
//! Requires `ARENA_DEV_UNSAFE=1` and installed tools; otherwise SKIP.

use arena_formal_checker::native::{NativeLeanRoute, VerifierRoute};
use arena_formal_checker::*;
use arena_types::{GateStatus, ObligationId};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Instant;

fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}
fn core_dir() -> PathBuf {
    crate_dir().join("../../formal-core")
}

fn hex_list(src: &str) -> String {
    let start = src.find('[').unwrap();
    let end = start + src[start..].find(']').unwrap();
    src[start..end]
        .split(|c: char| c == ',' || c == '[' || c.is_whitespace())
        .filter(|t| t.starts_with("0x"))
        .map(|t| t.trim_start_matches("0x").to_lowercase())
        .collect()
}

fn expected() -> TemplateExpected {
    let art = std::fs::read_to_string(core_dir().join("Toy/Artifacts.lean")).unwrap();
    let i = art.find("def publicDigest").unwrap();
    TemplateExpected {
        module: "ArenaExpected".into(),
        decl: "ArenaExpected.expectedTypeFor".into(),
        template: std::fs::read_to_string(crate_dir().join("tests/native/Expected.lean.tmpl")).unwrap(),
        data: BTreeMap::from([("public_digest".into(), LeanValue::Bytes(hex_list(&art[i..])))]),
    }
}

fn candidate(dest: &Path, model: &str) {
    let _ = std::fs::remove_dir_all(dest);
    std::fs::create_dir_all(dest.join("Toy")).unwrap();
    std::fs::create_dir_all(dest.join("Candidate")).unwrap();
    for m in ["Programs", "BytecodeProofs", "Artifacts", "Certificate"] {
        std::fs::copy(core_dir().join(format!("Toy/{m}.lean")), dest.join(format!("Toy/{m}.lean"))).unwrap();
    }
    std::fs::copy(crate_dir().join("tests/native/Candidate.lean"), dest.join("Candidate.lean")).unwrap();
    std::fs::copy(crate_dir().join(format!("tests/native/models/{model}.lean")), dest.join("Candidate/Model.lean")).unwrap();
}

/// Run the judge-built verifier on the toy instance (CONTRACTS §4 CLI).
fn run_verifier(bin: &Path, dir: &Path, claim: &[u8]) -> i32 {
    // public tape = Toy.toyPub = sha256 toyTable; proof = the table "ARNA".
    let toy_pub = [
        44u8, 87, 180, 217, 243, 243, 188, 83, 27, 45, 6, 189, 46, 109, 250, 247, 174, 214, 4, 61, 253, 192, 74, 102, 105, 43,
        128, 13, 219, 99, 220, 53,
    ];
    std::fs::create_dir_all(dir.join("public")).unwrap();
    std::fs::write(dir.join("public/public.bin"), toy_pub).unwrap();
    std::fs::write(dir.join("claim.bin"), claim).unwrap();
    std::fs::write(dir.join("proof.bin"), [0x41, 0x52, 0x4E, 0x41]).unwrap();
    std::process::Command::new(bin)
        .args(["--public", dir.join("public").to_str().unwrap()])
        .args(["--claim", dir.join("claim.bin").to_str().unwrap()])
        .args(["--proof", dir.join("proof.bin").to_str().unwrap()])
        .status()
        .unwrap()
        .code()
        .unwrap_or(-1)
}

struct Case {
    name: &'static str,
    model: &'static str,
    route: fn(&Path) -> VerifierRoute,
    /// (gate, status, acceptable codes) — `None` gate = every gate.
    expect: Vec<(Option<ObligationId>, GateStatus, Vec<&'static str>)>,
}

fn native(_: &Path) -> VerifierRoute {
    VerifierRoute::NativeLean(NativeLeanRoute::new("Candidate.Model.verify", "Candidate.Model"))
}

#[test]
fn native_lean_route() {
    if std::env::var("ARENA_DEV_UNSAFE").as_deref() != Ok("1") {
        eprintln!("SKIP native_lean_route: ARENA_DEV_UNSAFE=1 required");
        return;
    }
    let tools = match toolchain::ToolPaths::discover() {
        Ok(t) => t,
        Err(e) => {
            eprintln!("SKIP native_lean_route: {e}");
            return;
        }
    };
    let checker = Arc::new(FormalChecker::new(tools, Box::new(BwrapDevRunner::new().unwrap())));
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("fc-native");
    let _ = std::fs::remove_dir_all(&root);
    let cache = root.join("cache");
    let trusted = vec![TrustedPackage {
        name: "formal-core".into(),
        src_root: core_dir(),
        include: Some(vec!["ArenaCore".into(), "Toy.Spec".into()]),
    }];
    let policy = Policy { reserved_prefixes: vec!["ArenaCore".into()], ..Policy::default() };
    use ObligationId::*;
    let fail_all = |codes: Vec<&'static str>| vec![(None, GateStatus::Fail, codes)];
    // Formal gates fail; the binary is still the judge build of the (rejected)
    // model, so ARTIFACT_BINDING itself may pass.
    let fail_formal = |codes: Vec<&'static str>| {
        [FormalSemanticSoundness, FormalSemanticCompleteness, FormalCryptoSoundness, FormalImplConnection, AxiomAudit]
            .into_iter()
            .map(|g| (Some(g), GateStatus::Fail, codes.clone()))
            .collect::<Vec<_>>()
    };
    let cases = vec![
        Case { name: "native_ok", model: "ok", route: native, expect: vec![(None, GateStatus::Pass, vec![])] },
        Case { name: "native_model_sorry", model: "sorry", route: native, expect: fail_formal(vec!["SORRY_FOUND"]) },
        Case { name: "native_model_axiom", model: "axiom", route: native, expect: fail_formal(vec!["FORBIDDEN_AXIOM"]) },
        Case { name: "native_model_native_decide", model: "native_decide", route: native, expect: fail_formal(vec!["NATIVE_EVAL_FOUND"]) },
        Case { name: "native_model_shadow", model: "shadow", route: native, expect: fail_all(vec!["SHADOWED_DEFINITION"]) },
        Case { name: "native_model_macro_hijack", model: "macro_hijack", route: native, expect: fail_all(vec!["ARTIFACT_BINDING_FAILED"]) },
        Case { name: "native_model_imports_lean", model: "imports_lean", route: native, expect: fail_all(vec!["ARTIFACT_BINDING_FAILED"]) },
        Case { name: "native_model_missing", model: "missing", route: native, expect: fail_all(vec!["ARTIFACT_BINDING_FAILED"]) },
        Case {
            name: "native_candidate_binary",
            model: "ok",
            route: |dir| {
                let p = dir.join("their-verify");
                std::fs::write(&p, b"\x7fELF candidate-built verifier").unwrap();
                let mut r = NativeLeanRoute::new("Candidate.Model.verify", "Candidate.Model");
                r.candidate_binary_digest = Some(digest::sha256_file(&p).unwrap());
                VerifierRoute::NativeLean(r)
            },
            expect: vec![
                (Some(ArtifactBinding), GateStatus::Fail, vec!["ARTIFACT_BINDING_FAILED"]),
                (Some(FormalSemanticSoundness), GateStatus::Pass, vec![]),
                (Some(AxiomAudit), GateStatus::Pass, vec![]),
            ],
        },
        Case { name: "candidate_native_no_model", model: "ok", route: |_| VerifierRoute::CandidateNative, expect: fail_all(vec!["ARTIFACT_BINDING_FAILED"]) },
    ];

    // Warm the trusted build serially (shared cache).
    {
        let d = root.join("warm");
        candidate(&d.join("formal"), "ok");
        let exp = expected();
        let _ = checker.check(&CheckRequest {
            formal_dir: d.join("formal"),
            certificate: "Candidate.certificate".into(),
            trusted: trusted.clone(),
            expected: &exp,
            challenge_digest: None,
            policy: policy.clone(),
            limits: Limits::default(),
            work_dir: d.join("work"),
            cache_dir: cache.clone(),
            route: native(&d),
        });
    }
    let failures = Arc::new(Mutex::new(Vec::<String>::new()));
    let queue = Arc::new(Mutex::new(cases));
    let mut hs = vec![];
    for _ in 0..4 {
        let (queue, failures, checker, trusted, policy, root, cache) =
            (queue.clone(), failures.clone(), checker.clone(), trusted.clone(), policy.clone(), root.clone(), cache.clone());
        hs.push(std::thread::spawn(move || loop {
            let Some(c) = queue.lock().unwrap().pop() else { break };
            let dir = root.join(c.name);
            candidate(&dir.join("formal"), c.model);
            let exp = expected();
            let t = Instant::now();
            let rep = checker.check(&CheckRequest {
                formal_dir: dir.join("formal"),
                certificate: "Candidate.certificate".into(),
                trusted: trusted.clone(),
                expected: &exp,
                challenge_digest: None,
                policy: policy.clone(),
                limits: Limits::default(),
                work_dir: dir.join("work"),
                cache_dir: cache.clone(),
                route: (c.route)(&dir),
            });
            let _ = std::fs::write(dir.join("report.json"), serde_json::to_string_pretty(&rep).unwrap());
            let name_of = |v: serde_json::Value| v.as_str().unwrap().to_string();
            let summary: Vec<String> = rep
                .gates
                .iter()
                .map(|g| {
                    format!(
                        "{}={}{:?}",
                        name_of(serde_json::to_value(g.gate).unwrap()),
                        name_of(serde_json::to_value(g.status).unwrap()),
                        g.reason_codes.iter().map(|c| name_of(serde_json::to_value(c).unwrap())).collect::<Vec<_>>()
                    )
                })
                .collect();
            eprintln!("{:<28} {:>6.1}s {}", c.name, t.elapsed().as_secs_f64(), summary.join(" "));
            let mut errs = vec![];
            for (gate, status, codes) in &c.expect {
                for g in rep.gates.iter().filter(|g| gate.is_none_or(|x| x == g.gate)) {
                    if g.status != *status {
                        errs.push(format!("{}: {:?} is {:?}, expected {:?}", c.name, g.gate, g.status, status));
                    }
                }
                if !codes.is_empty() {
                    let got: Vec<String> = rep
                        .gates
                        .iter()
                        .filter(|g| gate.is_none_or(|x| x == g.gate))
                        .flat_map(|g| g.reason_codes.iter().map(|c| name_of(serde_json::to_value(c).unwrap())))
                        .collect();
                    if !codes.iter().any(|c| got.iter().any(|g| g == c)) {
                        errs.push(format!("{}: codes {got:?}, expected one of {codes:?}", c.name));
                    }
                }
            }
            if !rep.gates.iter().any(|g| g.gate == ArtifactBinding) {
                errs.push(format!("{}: no ARTIFACT_BINDING gate", c.name));
            }
            if c.name == "native_ok" {
                let nb = rep.native_verifier.as_ref().expect("judge-built verifier");
                assert_eq!(digest::sha256_file(&nb.path).unwrap(), nb.digest);
                let ok = run_verifier(&nb.path, &dir.join("run"), &[0, 0x41]);
                let bad = run_verifier(&nb.path, &dir.join("run"), &[0, 0x42]);
                if (ok, bad) != (0, 1) {
                    errs.push(format!("native_ok: judge-built verifier exit codes accept={ok} reject={bad}, expected 0/1"));
                }
                let g = &rep.evidence_graph;
                let model_node = g.nodes.iter().any(|n| n.id == "formal:verifier_model" && n.kind == arena_types::evidence::NodeKind::BackendSemantics);
                let trusted_edge = g.edges.iter().any(|e| {
                    e.from == "artifact:verifier_binary" && e.kind == "implements" && e.status == arena_types::evidence::EdgeStatus::Trusted
                });
                if !(model_node && trusted_edge) {
                    errs.push("native_ok: evidence graph lacks backend_semantics model node / trusted implements edge".into());
                }
                eprintln!("    judge-built verify {} accept={ok} reject={bad}", nb.digest);
            }
            if !errs.is_empty() {
                for f in &rep.findings {
                    eprintln!("    finding: {:?} {}", f.code, f.detail.lines().next().unwrap_or(""));
                }
            }
            failures.lock().unwrap().extend(errs);
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    let f = failures.lock().unwrap();
    assert!(f.is_empty(), "{}", f.join("\n"));
}
