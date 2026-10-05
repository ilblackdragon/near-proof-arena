//! FORMAL_CHECK builds the trusted reference only from the frozen trusted
//! tree the challenge pins (`formal_spec.tree_digest`), re-verified on the
//! job's own copy. A missing, tampered or wrong (e.g. HEAD-drifted) tree
//! fails the job as INFRA_ERROR before anything is built; nothing ever
//! falls back to a checkout. Cheap: every case stops before any Lean step.

mod common;

use arena_jobs::*;
use arena_types::{CandidateManifest, ChallengeDefinition, Digest, GateStatus, VerifiedSurface};
use arena_worker::executor::{ExecError, FormalEnv, JobExecutor};
use common::*;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;

const NEAR: &str = "chl_fefb6bc7596a6fb1a145062c864db947"; // near-transfer-receipt-v1-3

fn near() -> ChallengeDefinition {
    serde_json::from_slice(&std::fs::read(repo().join(format!("challenges/{NEAR}.json"))).unwrap())
        .unwrap()
}

/// A FORMAL_CHECK job for the toy package (no `[formal]` section: a run that
/// gets past the trusted-tree gate ends with UNKNOWN / CERTIFICATE_MISSING).
fn job(f: &Fixture, chal: &ChallengeDefinition) -> JobSpec {
    let files = package_files();
    let manifest =
        CandidateManifest::parse(std::str::from_utf8(&files["candidate.toml"].1).unwrap()).unwrap();
    let pkg = f.put(&tar_of(&files));
    let mut ctx = f.ctx(&pkg);
    ctx.challenge_id = NEAR.into();
    ctx.challenge_digest = chal.digest().unwrap();
    ctx.tier = f.exec.tier_cap();
    let d = Digest::of_bytes(b"x");
    let build = BuildOutputs {
        prepare: d.clone(),
        prove: d.clone(),
        verify: d.clone(),
        bundle: d.clone(),
        public_artifacts: d.clone(),
        formal_tree: d.clone(),
        certificate_decl: String::new(),
        toolchain_image: None,
        build_ns: None,
        bundle_archive: None,
        public_archive: None,
        native_verifier: None,
        verifier_bytecode: None,
    };
    let verified_surface = VerifiedSurface {
        challenge_id: NEAR.into(),
        verify_artifact: d.clone(),
        prepare_artifact: d.clone(),
        public_artifacts: d.clone(),
        formal_tree: d.clone(),
        certificate_decl: String::new(),
        checker_image: chal.toolchain_policy.checker_image.clone(),
        verify_route: None,
        verifier_bytecode: None,
        verifier_model: None,
        verifier_model_module: None,
    };
    JobSpec::FormalCheck(FormalCheckJob {
        ctx,
        challenge: chal.clone(),
        manifest,
        build,
        verified_surface,
    })
}

fn with_store(f: &mut Fixture, store: Option<PathBuf>) {
    f.exec.ctx.formal = Some(FormalEnv {
        trusted_trees: store,
        configs_dir: repo().join("runners/formal-checker/challenges"),
        images_dir: None,
    });
}

fn run(f: &Fixture, chal: &ChallengeDefinition) -> Result<JobResult, ExecError> {
    f.exec.execute(&job(f, chal), "fc", &AtomicBool::new(false))
}

fn infra(r: Result<JobResult, ExecError>, want: &str) {
    match r {
        Err(ExecError::Infra(m)) => assert!(m.contains(want), "{m}"),
        Err(e) => panic!("want INFRA ({want}), got {e}"),
        Ok(o) => panic!(
            "want INFRA ({want}), got a result: {:?}",
            o.gates
                .iter()
                .map(|g| (g.gate, g.status))
                .collect::<Vec<_>>()
        ),
    }
}

/// Copy a tree (no permissions games: the store's entry is test-owned).
fn copy_dir(from: &Path, to: &Path) {
    for e in arena_types::tree_entries(from).unwrap() {
        let t = to.join(&e.path);
        std::fs::create_dir_all(t.parent().unwrap()).unwrap();
        std::fs::copy(from.join(&e.path), t).unwrap();
    }
}

#[test]
fn formal_check_requires_the_pinned_trusted_tree() {
    let mut f = fixture();
    let chal = near();
    let pin = chal.semantic_scope.formal_spec.tree_digest.clone();

    // No store configured: fail closed.
    with_store(&mut f, None);
    infra(run(&f, &chal), "ARENA_TRUSTED_TREES");

    // Store without the pinned tree.
    let empty = f.tmp.path().join("empty-store");
    std::fs::create_dir_all(&empty).unwrap();
    with_store(&mut f, Some(empty));
    infra(run(&f, &chal), "not in the store");

    // HEAD's formal-core + spec/lean published under the pin's name: the
    // drift the pin exists to catch (refused unless HEAD equals the pin).
    let wrong = f.tmp.path().join("wrong-store");
    let head = f.tmp.path().join("head");
    assert!(extract_trusted("HEAD", &head).is_some());
    let head_digest = arena_types::trusted_tree::digest_of(&head).unwrap();
    if head_digest != pin {
        copy_dir(&head, &arena_types::trusted_tree::entry_dir(&wrong, &pin));
        with_store(&mut f, Some(wrong));
        infra(run(&f, &chal), "not the pinned");
    }

    let Some(store) = frozen_store(f.tmp.path(), &chal, NEAR_V1_TRUSTED_COMMIT) else {
        eprintln!("skipped (correct/tampered cases): {NEAR_V1_TRUSTED_COMMIT} not in this clone");
        return;
    };

    // The correct tree: the gate passes; the run continues (and here stops
    // at the toy package's missing [formal] section, never at the tree).
    with_store(&mut f, Some(store.clone()));
    let out = run(&f, &chal).expect("correct pinned tree is accepted");
    let log = out.log_excerpt.clone().unwrap_or_default();
    assert!(
        log.contains(&format!("trusted tree {pin}")) && log.contains("re-verified"),
        "{log}"
    );
    assert!(out.gates.iter().all(|g| g.status != GateStatus::Pass));

    // Tampered after publication (one judge module edited in place).
    let core =
        arena_types::trusted_tree::entry_dir(&store, &pin).join("formal-core/ArenaCore.lean");
    let mut src = std::fs::read_to_string(&core).unwrap();
    src.push_str("\naxiom ArenaCore.tampered : False\n");
    std::fs::write(&core, src).unwrap();
    infra(run(&f, &chal), "not the pinned");
}
