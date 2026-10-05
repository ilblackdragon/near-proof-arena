//! The NEAR challenge's judge configuration end to end: trusted packages
//! formal-core + spec/lean (NearSpec) from
//! `challenges/near-transfer-receipt-v1.json`, taken from the **frozen trusted
//! tree the signed challenge pins** (`formal_spec.tree_digest`, extracted from
//! its freeze commit and re-hashed), the Expected module rendered from that
//! tree's `spec/lean/judge/Expected.lean.template`, and two negative
//! candidates. Proves
//! the reference build of the real NEAR statement works (a FAIL with the right
//! reason code, never INFRA_ERROR/UNKNOWN). Opt-in: `FC_NEAR_SPEC=1`,
//! `ARENA_DEV_UNSAFE=1` and installed tools.

use arena_formal_checker::*;
use arena_types::GateStatus;
use std::path::{Path, PathBuf};

/// Copy git-tracked files of `rel` (clean checkout: no `.lake/`).
fn export(repo: &Path, rel: &str, dest: &Path) {
    let out = std::process::Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(["ls-files", "--", rel])
        .output()
        .unwrap();
    for f in String::from_utf8(out.stdout).unwrap().lines() {
        let d = dest.join(f);
        std::fs::create_dir_all(d.parent().unwrap()).unwrap();
        std::fs::copy(repo.join(f), d).unwrap();
    }
}

#[test]
fn near_transfer_expected_reference_build() {
    if std::env::var("FC_NEAR_SPEC").as_deref() != Ok("1")
        || std::env::var("ARENA_DEV_UNSAFE").as_deref() != Ok("1")
    {
        eprintln!(
            "SKIP near_transfer_expected_reference_build: set FC_NEAR_SPEC=1 ARENA_DEV_UNSAFE=1"
        );
        return;
    }
    let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap();
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("fc-near-spec");
    let _ = std::fs::remove_dir_all(&root);
    let clean = root.join("clean");
    export(&repo, "formal-core", &clean);
    export(&repo, "spec/lean", &clean);
    // The frozen tree chl_5ef2… (NEAR v1 family) pins.
    let chal: arena_types::ChallengeDefinition = serde_json::from_slice(
        &std::fs::read(repo.join("challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json")).unwrap(),
    )
    .unwrap();
    let pin = chal.semantic_scope.formal_spec.tree_digest.clone();
    let store = root.join("trusted-trees");
    let entry = arena_types::trusted_tree::entry_dir(&store, &pin);
    std::fs::create_dir_all(&entry).unwrap();
    let st = std::process::Command::new("sh")
        .arg("-c")
        .arg("git -C \"$1\" archive --format=tar 6873c9980fd93c0483e93b94fe7e8a1fe0d52d52 -- formal-core spec/lean | tar -x -C \"$2\"")
        .arg("sh")
        .arg(&repo)
        .arg(&entry)
        .status()
        .unwrap();
    assert!(
        st.success(),
        "freeze commit of the NEAR v1 pin not in this clone"
    );
    let frozen = root.join("frozen");
    arena_types::trusted_tree::materialize(&store, &pin, &frozen).unwrap();
    let cfg = ChallengeFormalConfig::load(
        &repo.join("runners/formal-checker/challenges/near-transfer-receipt-v1.json"),
    )
    .unwrap();
    let profile: arena_types::SecurityProfile = serde_json::from_slice(
        &std::fs::read(repo.join("security/profiles/validity-classical-128.json")).unwrap(),
    )
    .unwrap();
    let exp = cfg
        .expected(
            &frozen,
            &ExpectedInputs {
                profile: &profile,
                verify_fuel: 1 << 30,
                max_proof_bytes: 8 << 20,
                max_reduction_fuel: 1 << 30,
                public_digest_hex: "ab".repeat(32),
                verifier_digest_hex: "cd".repeat(32),
            },
        )
        .unwrap();
    let tools = toolchain::ToolPaths::discover().expect("tools");
    let checker = FormalChecker::new(tools, Box::new(dev_runner().unwrap()));
    let policy = Policy {
        reserved_prefixes: cfg.reserved_prefixes.clone(),
        ..Policy::default()
    };
    let cases = [
        ("sorry", "import ArenaExpected\ntheorem Candidate.certificate : ArenaExpected.expectedType := sorry\n", "SORRY_FOUND"),
        ("wrong_type", "import ArenaExpected\ntheorem Candidate.certificate : True := trivial\n", "THEOREM_TYPE_MISMATCH"),
    ];
    let mut failures = vec![];
    for (name, src, code) in cases {
        let formal = root.join(name).join("formal");
        std::fs::create_dir_all(&formal).unwrap();
        std::fs::write(formal.join("Candidate.lean"), src).unwrap();
        let req = CheckRequest {
            formal_dir: formal,
            certificate: "Candidate.certificate".into(),
            trusted: cfg.trusted_packages(&frozen),
            expected: &exp,
            challenge_digest: None,
            trusted_tree: Some(pin.clone()),
            policy: policy.clone(),
            limits: Limits::default(),
            work_dir: root.join(name).join("work"),
            cache_dir: root.join("cache"),
            route: Default::default(),
        };
        let rep = checker.check(&req);
        let codes: Vec<String> = rep
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
            .collect();
        eprintln!(
            "{name}: {:?} {codes:?}",
            rep.gates.iter().map(|g| g.status).collect::<Vec<_>>()
        );
        if !rep.gates.iter().any(|g| g.status == GateStatus::Fail)
            || !codes.iter().any(|c| c == code)
        {
            failures.push(format!(
                "{name}: {codes:?} findings {:?}",
                rep.findings
                    .iter()
                    .map(|f| f.detail.lines().next().unwrap_or("").to_string())
                    .collect::<Vec<_>>()
            ));
        }
    }
    // The v1 family's pinned tree predates the native-lean template: that
    // route has no statement under these challenges (the worker fails it as
    // INFRA_ERROR); it takes a challenge that pins a tree containing it.
    assert!(cfg
        .expected_native_lean(
            &frozen,
            &ExpectedInputs {
                profile: &profile,
                verify_fuel: 1 << 30,
                max_proof_bytes: 8 << 20,
                max_reduction_fuel: 1 << 30,
                public_digest_hex: "ab".repeat(32),
                verifier_digest_hex: String::new(),
            },
        )
        .is_err());
    // native-lean route (HEAD tree, no pinned challenge): the NEAR native
    // template elaborates with a candidate model spliced in and the judge's
    // own build digest (a sorry certificate must be reported as SORRY_FOUND,
    // never INFRA_ERROR).
    {
        let exp_native = cfg
            .expected_native_lean(
                &clean,
                &ExpectedInputs {
                    profile: &profile,
                    verify_fuel: 1 << 30,
                    max_proof_bytes: 8 << 20,
                    max_reduction_fuel: 1 << 30,
                    public_digest_hex: "ab".repeat(32),
                    verifier_digest_hex: String::new(),
                },
            )
            .unwrap();
        let formal = root.join("native_sorry").join("formal");
        std::fs::create_dir_all(formal.join("Candidate")).unwrap();
        std::fs::write(
            formal.join("Candidate/Model.lean"),
            "import ArenaCore.Verifier\n\ndef Candidate.Model.verify : ArenaCore.OracleVerifier :=\n  ArenaCore.interpOracleVerifier [] 0\n",
        )
        .unwrap();
        std::fs::write(
            formal.join("Candidate.lean"),
            "import ArenaExpectedInst\ntheorem Candidate.certificate : ArenaExpectedInst.expectedType := sorry\n",
        )
        .unwrap();
        let rep = checker.check(&CheckRequest {
            formal_dir: formal,
            certificate: "Candidate.certificate".into(),
            trusted: cfg.trusted_packages(&clean),
            expected: &exp_native,
            challenge_digest: None,
            trusted_tree: None,
            policy: policy.clone(),
            limits: Limits::default(),
            work_dir: root.join("native_sorry").join("work"),
            cache_dir: root.join("cache"),
            route: native::VerifierRoute::NativeLean(native::NativeLeanRoute::new(
                "Candidate.Model.verify",
                "Candidate.Model",
            )),
        });
        let codes: Vec<String> = rep
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
            .collect();
        eprintln!(
            "native_sorry: {:?} {codes:?} binary={:?}",
            rep.gates.iter().map(|g| g.status).collect::<Vec<_>>(),
            rep.native_verifier.as_ref().map(|n| n.digest.to_string())
        );
        if rep.native_verifier.is_none()
            || !codes.iter().any(|c| c == "SORRY_FOUND")
            || codes.iter().any(|c| c == "INFRA_ERROR")
        {
            failures.push(format!(
                "native_sorry: {codes:?} findings {:?}",
                rep.findings
                    .iter()
                    .map(|f| f.detail.lines().next().unwrap_or("").to_string())
                    .collect::<Vec<_>>()
            ));
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
