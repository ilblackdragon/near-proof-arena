//! Integration with the real formal-core (`ArenaCore`) and its worked Toy
//! backend. Opt-in: `FC_FORMAL_CORE_DIR=<path to formal-core/>` plus
//! `ARENA_DEV_UNSAFE=1` and installed tools.
//!
//! * trusted: `ArenaCore.*` + the challenge spec `Toy.Spec`;
//! * judge-generated Expected module: `Toy.Artifacts` (`ToyJudge.Expected`),
//!   regenerated from a template with the artifact digests as data;
//! * candidate: `Toy.Programs`, `Toy.BytecodeProofs`, `Toy.Certificate`, and
//!   each of formal-core's `negative/*.lean` files as `Candidate.lean`.
#![allow(clippy::type_complexity, clippy::doc_lazy_continuation)]

use arena_formal_checker::*;
use arena_types::GateStatus;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

fn hex_list(src: &str) -> (String, std::ops::Range<usize>) {
    let start = src.find('[').unwrap();
    let end = start + src[start..].find(']').unwrap() + 1;
    let hex: String = src[start..end]
        .split(|c: char| c == ',' || c == '[' || c == ']' || c.is_whitespace())
        .filter(|t| t.starts_with("0x"))
        .map(|t| t.trim_start_matches("0x").to_lowercase())
        .collect();
    (hex, start..end)
}

/// Turn formal-core's hand-written `Toy/Artifacts.lean` into a judge template.
fn template(core: &Path) -> (String, String, String) {
    let src = std::fs::read_to_string(core.join("Toy/Artifacts.lean")).unwrap();
    let i = src.find("def publicDigest").unwrap();
    let (pub_hex, r1) = hex_list(&src[i..]);
    let mut t = format!(
        "{}{{{{public_digest}}}}{}",
        &src[..i + r1.start],
        &src[i + r1.end..]
    );
    let j = t.find("def verifierDigest").unwrap();
    let (ver_hex, r2) = hex_list(&t[j..]);
    t = format!(
        "{}{{{{verifier_digest}}}}{}",
        &t[..j + r2.start],
        &t[j + r2.end..]
    );
    (t, pub_hex, ver_hex)
}

fn expected(t: &str, pub_hex: &str, ver_hex: &str) -> TemplateExpected {
    TemplateExpected {
        module: "Toy.Artifacts".into(),
        decl: "ToyJudge.Expected".into(),
        template: t.into(),
        data: BTreeMap::from([
            ("public_digest".into(), LeanValue::Bytes(pub_hex.into())),
            ("verifier_digest".into(), LeanValue::Bytes(ver_hex.into())),
        ]),
    }
}

fn candidate_dir(core: &Path, dest: &Path, extra: Option<&Path>) {
    let _ = std::fs::remove_dir_all(dest);
    std::fs::create_dir_all(dest.join("Toy")).unwrap();
    for m in ["Programs", "BytecodeProofs", "Certificate"] {
        std::fs::copy(
            core.join(format!("Toy/{m}.lean")),
            dest.join(format!("Toy/{m}.lean")),
        )
        .unwrap();
    }
    if let Some(e) = extra {
        std::fs::copy(e, dest.join("Candidate.lean")).unwrap();
    }
}

#[test]
fn formal_core_toy() {
    let Ok(core) = std::env::var("FC_FORMAL_CORE_DIR") else {
        eprintln!("SKIP formal_core_toy: set FC_FORMAL_CORE_DIR=<formal-core dir>");
        return;
    };
    if std::env::var("ARENA_DEV_UNSAFE").as_deref() != Ok("1") {
        eprintln!("SKIP formal_core_toy: ARENA_DEV_UNSAFE=1 required");
        return;
    }
    let core = PathBuf::from(core);
    let tools = toolchain::ToolPaths::discover().expect("tools");
    let checker = FormalChecker::new(tools, Box::new(dev_runner().unwrap()));
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("fc-formal-core");
    let _ = std::fs::remove_dir_all(&root);
    let cache = root.join("cache");
    let (tmpl, pub_hex, ver_hex) = template(&core);
    let good = expected(&tmpl, &pub_hex, &ver_hex);
    let trusted = vec![TrustedPackage {
        name: "formal-core".into(),
        src_root: core.clone(),
        include: Some(vec!["ArenaCore".into(), "Toy.Spec".into()]),
    }];
    let policy = Policy {
        reserved_prefixes: vec!["ArenaCore".into()],
        ..Policy::default()
    };

    // (name, extra candidate file, certificate, expected data, expected status, acceptable codes)
    let mut cases: Vec<(
        String,
        Option<PathBuf>,
        String,
        TemplateExpected,
        GateStatus,
        Vec<&str>,
    )> = vec![(
        "toy_certificate".into(),
        None,
        "Toy.certificate".into(),
        good.clone(),
        GateStatus::Pass,
        vec![],
    )];
    let mut stale_ver = hex::decode(&ver_hex).unwrap();
    *stale_ver.last_mut().unwrap() ^= 1;
    cases.push((
        "toy_stale_digest".into(),
        None,
        "Toy.certificate".into(),
        expected(&tmpl, &pub_hex, &hex::encode(stale_ver)),
        GateStatus::Fail,
        vec!["BUILD_FAILED", "CERTIFICATE_MISSING"],
    ));
    let mut negs: Vec<PathBuf> = std::fs::read_dir(core.join("negative"))
        .into_iter()
        .flatten()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "lean"))
        .collect();
    negs.sort();
    for n in negs {
        let src = std::fs::read_to_string(&n).unwrap();
        let line = src
            .lines()
            .find(|l| l.starts_with("-- EXPECT:"))
            .unwrap_or("")
            .to_string();
        let (status, codes) = if line.contains("PASS") {
            (GateStatus::Pass, vec![])
        } else {
            let mut c: Vec<&str> = [
                "SORRY_FOUND",
                "FORBIDDEN_AXIOM",
                "UNAPPROVED_ASSUMPTION",
                "NATIVE_EVAL_FOUND",
                "THEOREM_TYPE_MISMATCH",
                "SHADOWED_DEFINITION",
            ]
            .into_iter()
            .filter(|k| line.contains(k))
            .collect();
            if line.contains("ARTIFACT_BINDING_FAILED") {
                c.extend(["BUILD_FAILED", "CERTIFICATE_MISSING"]);
            }
            (GateStatus::Fail, c)
        };
        cases.push((
            n.file_stem().unwrap().to_str().unwrap().to_string(),
            Some(n.clone()),
            "Candidate.certificate".into(),
            good.clone(),
            status,
            codes,
        ));
    }

    let mut failures = Vec::new();
    for (name, extra, cert, exp, status, codes) in &cases {
        let formal = root.join(name).join("formal");
        candidate_dir(&core, &formal, extra.as_deref());
        let req = CheckRequest {
            formal_dir: formal,
            certificate: cert.clone(),
            trusted: trusted.clone(),
            expected: exp,
            challenge_digest: None,
            trusted_tree: None,
            policy: policy.clone(),
            limits: Limits::default(),
            work_dir: root.join(name).join("work"),
            cache_dir: cache.clone(),
            route: Default::default(),
        };
        let t = Instant::now();
        let rep = checker.check(&req);
        let got: Vec<String> = rep
            .gates
            .iter()
            .flat_map(|g| {
                g.reason_codes.iter().map(|c| {
                    serde_json::to_value(c)
                        .unwrap()
                        .as_str()
                        .unwrap()
                        .to_string()
                })
            })
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect();
        let statuses: Vec<GateStatus> = rep.gates.iter().map(|g| g.status).collect();
        eprintln!(
            "{name:<32} {:>6.1}s {:?} {:?}",
            t.elapsed().as_secs_f64(),
            statuses[0],
            got
        );
        let _ = std::fs::write(
            root.join(name).join("report.json"),
            serde_json::to_string_pretty(&rep).unwrap(),
        );
        if !statuses.iter().all(|s| s == status) {
            failures.push(format!(
                "{name}: statuses {statuses:?}, expected all {status:?}; findings {:?}",
                rep.findings
                    .iter()
                    .map(|f| (&f.code, f.detail.lines().next()))
                    .collect::<Vec<_>>()
            ));
        } else if !codes.is_empty() && !codes.iter().any(|c| got.iter().any(|g| g == c)) {
            failures.push(format!("{name}: codes {got:?}, expected one of {codes:?}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn dev_runner() -> Result<SandboxRunner, arena_formal_checker::sandbox::InfraError> {
    let helper = arena_sandbox::HelperCommand {
        exe: env!("CARGO_BIN_EXE_formal-check").into(),
        prefix_args: vec![arena_formal_checker::HELPER_ARG.into()],
    };
    let work = std::env::temp_dir().join(format!(
        "fc-sandbox-{}-{}",
        env!("CARGO_CRATE_NAME"),
        std::process::id()
    ));
    SandboxRunner::bwrap_dev(helper, work)
}
