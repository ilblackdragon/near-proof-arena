//! FORMAL_CHECK end to end through the worker (bwrap-dev; firecracker with
//! the lean-checker image when `ARENA_FC_TESTS=1`): the NEAR challenge's real
//! judge configuration (formal-core + spec/lean, Expected template bound to
//! the judge-built artifact digests). Slow (reference build of the NEAR
//! statement): opt-in with `ARENA_FORMAL_TESTS=1`.

mod common;

use arena_jobs::*;
use arena_types::{ChallengeDefinition, GateStatus, ObligationId, ReasonCode, VerifiedSurface};
use arena_worker::executor::{FormalEnv, JobExecutor};
use common::*;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

const NEAR: &str = "chl_5ef2bc7d2068219635426e47ca46bfbb";

fn candidate(cert: &str) -> std::collections::BTreeMap<String, (u32, Vec<u8>)> {
    let mut files = package_files();
    let m = String::from_utf8(files["candidate.toml"].1.clone())
        .unwrap()
        .replace(CHALLENGE, NEAR)
        + "\n[formal]\nlean_project = \"formal\"\ncertificate = \"Candidate.certificate\"\n";
    set(&mut files, "candidate.toml", &m);
    // The statement pins sha256(public_dir/public.bin).
    let p = String::from_utf8(files["source/prepare.c"].1.clone())
        .unwrap()
        .replace("\"%s/key\"", "\"%s/public.bin\"");
    set(&mut files, "source/prepare.c", &p);
    let p = String::from_utf8(files["source/prove.c"].1.clone())
        .unwrap()
        .replace("\"%s/key\"", "\"%s/public.bin\"");
    set(&mut files, "source/prove.c", &p);
    let v = String::from_utf8(files["source/verify.c"].1.clone())
        .unwrap()
        .replace("\"%s/key\"", "\"%s/public.bin\"");
    set(&mut files, "source/verify.c", &v);
    files.insert(
        "formal/Candidate.lean".into(),
        (0o644, cert.as_bytes().to_vec()),
    );
    files
}

fn run_formal(
    f: &Fixture,
    exec: &arena_worker::executor::StageExecutor,
    chal: &ChallengeDefinition,
    cert: &str,
) -> JobResult {
    let files = candidate(cert);
    let pkg = f.put(&tar_of(&files));
    let mut ctx = f.ctx(&pkg);
    ctx.challenge_id = NEAR.into();
    ctx.challenge_digest = chal.digest().unwrap();
    // The bwrap-dev worker only takes demo-tier jobs; the formal pipeline
    // itself is identical.
    ctx.tier = exec.tier_cap();
    // Validate + build on the bwrap-dev fixture (demo-tier context).
    let mut demo_ctx = ctx.clone();
    demo_ctx.tier = arena_types::challenge::Tier::Demo;
    let v = f
        .exec
        .execute(
            &JobSpec::Validate(ValidateJob {
                ctx: demo_ctx.clone(),
                challenge: chal.clone(),
            }),
            "v",
            &AtomicBool::new(false),
        )
        .unwrap();
    assert_eq!(
        v.gates[0].status,
        GateStatus::Pass,
        "{}",
        v.gates[0].summary
    );
    let manifest = v.manifest.unwrap();
    let b = f
        .exec
        .execute(
            &JobSpec::Build(BuildJob {
                ctx: demo_ctx,
                challenge: chal.clone(),
                manifest: manifest.clone(),
            }),
            "b",
            &AtomicBool::new(false),
        )
        .unwrap();
    assert_eq!(
        b.gates[0].status,
        GateStatus::Pass,
        "{}",
        b.gates[0].summary
    );
    let build = b.build.unwrap();
    let vs = VerifiedSurface {
        challenge_id: NEAR.into(),
        verify_artifact: build.verify.clone(),
        prepare_artifact: build.prepare.clone(),
        public_artifacts: build.public_artifacts.clone(),
        formal_tree: build.formal_tree.clone(),
        certificate_decl: build.certificate_decl.clone(),
        checker_image: chal.toolchain_policy.checker_image.clone(),
        verify_route: manifest.entry.verify_route,
        verifier_bytecode: build.verifier_bytecode.clone(),
        verifier_model: manifest
            .formal
            .as_ref()
            .and_then(|f| f.verifier_model.clone()),
        verifier_model_module: manifest
            .formal
            .as_ref()
            .and_then(|f| f.verifier_model_module.clone()),
    };
    exec.execute(
        &JobSpec::FormalCheck(FormalCheckJob {
            ctx,
            challenge: chal.clone(),
            manifest,
            build,
            verified_surface: vs,
        }),
        "fc",
        &AtomicBool::new(false),
    )
    .unwrap()
}

fn has(r: &JobResult, g: ObligationId, status: GateStatus, rc: Option<ReasonCode>) {
    let x = gate(r, g);
    assert_eq!(
        x.status, status,
        "{g:?}: {} {:?}",
        x.summary, x.reason_codes
    );
    if let Some(rc) = rc {
        assert!(x.reason_codes.contains(&rc), "{g:?}: {:?}", x.reason_codes);
    }
}

fn formal_env(tmp: &Path, images: Option<PathBuf>) -> FormalEnv {
    // The frozen trusted tree the NEAR challenge pins (never HEAD's).
    let store = frozen_store(tmp, &near(), NEAR_V1_TRUSTED_COMMIT)
        .expect("the pinned trusted tree's commit is in this clone");
    FormalEnv {
        trusted_trees: Some(store),
        configs_dir: repo().join("runners/formal-checker/challenges"),
        images_dir: images,
    }
}

fn near() -> ChallengeDefinition {
    serde_json::from_slice(&std::fs::read(repo().join(format!("challenges/{NEAR}.json"))).unwrap())
        .unwrap()
}

fn negatives(f: &Fixture, exec: &arena_worker::executor::StageExecutor, chal: ChallengeDefinition) {
    let r = run_formal(f, exec, &chal, "import ArenaExpected\ntheorem Candidate.certificate : ArenaExpected.expectedType := sorry\n");
    for g in &r.gates {
        eprintln!("sorry: {:?} {:?} {:?}", g.gate, g.status, g.reason_codes);
    }
    has(
        &r,
        ObligationId::AxiomAudit,
        GateStatus::Fail,
        Some(ReasonCode::SorryFound),
    );
    assert_ne!(
        gate(&r, ObligationId::ArtifactBinding).status,
        GateStatus::Pass
    );

    let r = run_formal(
        f,
        exec,
        &chal,
        "import ArenaExpected\ntheorem Candidate.certificate : True := trivial\n",
    );
    for g in &r.gates {
        eprintln!(
            "wrong-type: {:?} {:?} {:?}",
            g.gate, g.status, g.reason_codes
        );
    }
    has(
        &r,
        ObligationId::FormalSemanticSoundness,
        GateStatus::Fail,
        Some(ReasonCode::TheoremTypeMismatch),
    );
    has(
        &r,
        ObligationId::ArtifactBinding,
        GateStatus::Fail,
        Some(ReasonCode::ArtifactBindingFailed),
    );
    assert!(r
        .gates
        .iter()
        .all(|g| g.status != GateStatus::Pass || g.gate == ObligationId::FormalZk));
}

#[test]
fn formal_check_near_statement_bwrap() {
    if std::env::var("ARENA_FORMAL_TESTS").as_deref() != Ok("1") {
        skip_gated!("set ARENA_FORMAL_TESTS=1");
        return;
    }
    let mut f = fixture();
    f.exec.ctx.formal = Some(formal_env(f.tmp.path(), None));
    assert!(f.exec.kinds().contains(&JobKind::FormalCheck));
    let exec = common::executor(
        f.exec.ctx.sandbox.clone(),
        f.store.clone(),
        &f.tmp.path().join("fjobs"),
    );
    let mut exec = exec;
    exec.ctx.formal = f.exec.ctx.formal.clone();
    // Test-only re-pin (as tests/near.rs): the signed challenge pins the
    // identity of one build of the host checker tools; this host's tools may
    // have been rebuilt. The trusted tree pin is left untouched.
    let mut chal = near();
    chal.toolchain_policy.checker_image = arena_formal_checker::toolchain::ToolPaths::discover()
        .unwrap()
        .image_digest()
        .unwrap();
    negatives(&f, &exec, chal);
}

#[test]
fn formal_check_near_statement_firecracker() {
    if std::env::var("ARENA_FORMAL_TESTS").as_deref() != Ok("1")
        || std::env::var("ARENA_FC_TESTS").as_deref() != Ok("1")
    {
        skip_gated!("set ARENA_FORMAL_TESTS=1 ARENA_FC_TESTS=1");
        return;
    }
    let f = fixture();
    let deps = std::env::var_os("ARENA_FC_DEPS")
        .map(PathBuf::from)
        .unwrap_or_else(|| "/data/illia/nearproof-deps/firecracker".into());
    let images = std::env::var_os("LEAN_CHECKER_IMAGES")
        .map(PathBuf::from)
        .unwrap_or_else(|| "/data/illia/nearproof-deps/lean-checker/images".into());
    let cfg =
        arena_firecracker::FirecrackerConfig::from_deps_dir(&deps, &deps.join("work-worker-tests"))
            .unwrap();
    let fc = arena_firecracker::FirecrackerSandbox::new(cfg).unwrap();
    let mut exec = common::executor(
        Arc::new(fc),
        f.store.clone(),
        &f.tmp.path().join("fc-fjobs"),
    );
    exec.ctx.formal = Some(formal_env(f.tmp.path(), Some(images.clone())));
    assert!(exec.kinds().contains(&JobKind::FormalCheck));
    // The signed NEAR challenge pins the host-installed dev checker's
    // identity, not the lean-checker image's: the worker refuses (UNKNOWN).
    let r = {
        let chal = near();
        run_formal(
            &f,
            &exec,
            &chal,
            "import ArenaExpected\ntheorem Candidate.certificate : True := trivial\n",
        )
    };
    assert!(r.gates.iter().all(|g| g.status == GateStatus::Unknown
        && g.summary.contains("not the challenge's pinned checker")));
    // With the image's identity pinned (test-only re-pin), the real checks run in microVMs.
    let meta = std::fs::read_dir(&images)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .find(|p| p.extension().is_some_and(|x| x == "json"))
        .unwrap();
    let meta: serde_json::Value = serde_json::from_slice(&std::fs::read(meta).unwrap()).unwrap();
    let dir = images.join(
        meta["digest"]
            .as_str()
            .unwrap()
            .trim_start_matches("sha256:"),
    );
    let tools = arena_formal_checker::toolchain::ToolPaths {
        lean_sysroot: dir.join("arena/tc"),
        lean4export: dir.join("arena/tools/lean4export"),
        nanoda: Some(dir.join("arena/tools/nanoda_bin")),
        lean4lean: Some(dir.join("arena/tools/lean4lean")),
        arena_audit: dir.join("arena/tools/arena-audit"),
    };
    let mut chal = near();
    chal.toolchain_policy.checker_image = tools.image_digest().unwrap();
    negatives(&f, &exec, chal);
}
