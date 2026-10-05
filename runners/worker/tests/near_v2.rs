//! Audit A04: the v2 draft challenge (`near-arena-claim-v2`,
//! `challenges/drafts/near-transfer-receipt-v2.draft.json`) through the real
//! worker pipeline — validate, build, conformance, adversarial, benchmark —
//! with the governed `near-arena-oracle --scope v2`, the v2 generator specs
//! (`spec/workloads/near-transfer-receipt-v2`) and the digest-pinned v2 public
//! fixtures (`oracle/fixtures/v2/public`). The candidate is the TEST-ONLY
//! `tests/e2e/near-v2-spec-candidate` (prove/verify via the Lean reference
//! `nearspec-check --scope v2`); no formal certificate exists for v2, so the
//! job tier is DEMO and FORMAL_CHECK is not run. The challenge is an
//! unsigned local TEST copy of the draft: the worker trusts the job's
//! challenge definition (signatures are checked server-side), and nothing
//! here touches a live deployment.
//!
//! Also: the same pipeline refuses wrong-version inputs (a v2 challenge fed
//! v1 fixtures) before any candidate code runs.
//!
//! Opt-in: `ARENA_NEAR_TESTS=1`, a `near-arena-oracle` with `--scope v2`
//! (`ARENA_NEAR_ORACLE`) and `nearspec-check` (`ARENA_NEARSPEC_CHECK`,
//! default `spec/lean/.lake/build/bin/nearspec-check` after
//! `lake build nearspec-check`).

mod common;

use arena_jobs::*;
use arena_types::{ChallengeDefinition, GateStatus, ObligationId};
use arena_worker::executor::{ExecError, JobExecutor};
use arena_worker::oracle::Oracles;
use common::*;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;

const TEST_CHALLENGE: &str = "chl_test_near_transfer_receipt_v2_local";
const CANDIDATE: &str = "tests/e2e/near-v2-spec-candidate";

fn git_files(rel: &str) -> std::collections::BTreeMap<String, (u32, Vec<u8>)> {
    let out = std::process::Command::new("git")
        .arg("-C")
        .arg(repo())
        .args(["ls-files", "-s", "--", rel])
        .output()
        .unwrap();
    let mut m = std::collections::BTreeMap::new();
    for l in String::from_utf8(out.stdout).unwrap().lines() {
        let (meta, path) = l.split_once('\t').unwrap();
        let mode = if meta.starts_with("100755") {
            0o755
        } else {
            0o644
        };
        m.insert(
            path.strip_prefix(&format!("{rel}/")).unwrap().to_string(),
            (mode, std::fs::read(repo().join(path)).unwrap()),
        );
    }
    m
}

/// A clean copy of the git-tracked files of `rel` (no build products).
fn export(rel: &str, dest: &Path) -> PathBuf {
    for (p, (_, b)) in git_files(rel) {
        let d = dest.join(rel).join(p);
        std::fs::create_dir_all(d.parent().unwrap()).unwrap();
        std::fs::write(d, b).unwrap();
    }
    dest.join(rel)
}

struct Env {
    f: Fixture,
    nearspec: PathBuf,
}

fn v2_env() -> Option<Env> {
    if std::env::var("ARENA_NEAR_TESTS").as_deref() != Ok("1") {
        skip_gated!("set ARENA_NEAR_TESTS=1");
        return None;
    }
    let oracle = std::env::var_os("ARENA_NEAR_ORACLE")
        .map(PathBuf::from)
        .unwrap_or_else(|| repo().join("oracle/target/debug/near-arena-oracle"));
    if !oracle.is_file() {
        skip_gated!("no near-arena-oracle at {}", oracle.display());
        return None;
    }
    let nearspec = std::env::var_os("ARENA_NEARSPEC_CHECK")
        .map(PathBuf::from)
        .unwrap_or_else(|| repo().join("spec/lean/.lake/build/bin/nearspec-check"));
    if !nearspec.is_file() {
        skip_gated!("no nearspec-check at {}", nearspec.display());
        return None;
    }
    let mut f = fixture();
    // Both NEAR oracles (v1 + v2) over both generator suites, both fixture
    // sets: selection is by claim encoding and digest only.
    let mut o = Oracles::builtin()
        .with_near_dirs(
            oracle,
            &[
                repo().join("spec/workloads/near-transfer-receipt-v1"),
                repo().join("spec/workloads/near-transfer-receipt-v2"),
            ],
        )
        .unwrap();
    let clean = f.tmp.path().join("clean");
    let v1 = o
        .add_fixtures_dir(&export("oracle/fixtures/public", &clean))
        .unwrap();
    let v2 = o
        .add_fixtures_dir(&export("oracle/fixtures/v2/public", &clean))
        .unwrap();
    f.chal = serde_json::from_slice::<ChallengeDefinition>(
        &std::fs::read(repo().join("challenges/drafts/near-transfer-receipt-v2.draft.json"))
            .unwrap(),
    )
    .unwrap();
    assert_eq!(f.chal.claim_encoding.format, "near-arena-claim-v2");
    assert_eq!(v2, f.chal.workload_suite.public_fixtures, "v2 fixture pin");
    assert_ne!(v1, v2);
    f.exec.ctx.oracles = o;
    f.exec.ctx.bench_batch_cap = Some(1);
    f.exec.ctx.conformance_samples = 3;
    Some(Env { f, nearspec })
}

fn ctx(f: &Fixture, pkg: &arena_types::Digest) -> JobContext {
    let mut c = f.ctx(pkg);
    c.challenge_id = TEST_CHALLENGE.into();
    c.challenge_digest = f.chal.digest().unwrap();
    c.tier = arena_types::challenge::Tier::Demo;
    c
}

fn run(f: &Fixture, spec: &JobSpec) -> Result<JobResult, ExecError> {
    let t = std::time::Instant::now();
    let r = f.exec.execute(spec, "near-v2", &AtomicBool::new(false));
    eprintln!("{}: {:?}", spec.kind(), t.elapsed());
    if let Ok(r) = &r {
        for g in &r.gates {
            eprintln!(
                "  {:?} {:?} {:?} {}",
                g.gate,
                g.status,
                g.reason_codes,
                &g.summary[..g.summary.len().min(400)]
            );
        }
    }
    r
}

fn package(nearspec: &Path) -> std::collections::BTreeMap<String, (u32, Vec<u8>)> {
    let mut files = git_files(CANDIDATE);
    files.insert(
        "bin/nearspec-check".into(),
        (0o755, std::fs::read(nearspec).unwrap()),
    );
    files
}

fn built(f: &Fixture, nearspec: &Path) -> ExecJob {
    let pkg = f.put(&tar_of(&package(nearspec)));
    let v = run(
        f,
        &JobSpec::Validate(ValidateJob {
            ctx: ctx(f, &pkg),
            challenge: f.chal.clone(),
        }),
    )
    .unwrap();
    assert_eq!(
        v.gates[0].status,
        GateStatus::Pass,
        "{}",
        v.gates[0].summary
    );
    let manifest = v.manifest.unwrap();
    let b = run(
        f,
        &JobSpec::Build(BuildJob {
            ctx: ctx(f, &pkg),
            challenge: f.chal.clone(),
            manifest: manifest.clone(),
        }),
    )
    .unwrap();
    assert_eq!(
        b.gates[0].status,
        GateStatus::Pass,
        "{}",
        b.gates[0].summary
    );
    ExecJob {
        ctx: ctx(f, &pkg),
        challenge: f.chal.clone(),
        manifest,
        build: b.build.unwrap(),
    }
}

#[test]
fn v2_draft_challenge_through_the_worker_pipeline() {
    let Some(Env { f, nearspec }) = v2_env() else {
        return;
    };
    let job = built(&f, &nearspec);
    // The judge-run prepare got the v2 params.bin (statement v1 id, v2
    // runtime-config digest), checked against the v2 pin.
    let c = run(&f, &JobSpec::Conformance(job.clone())).unwrap();
    for g in &c.gates {
        assert_eq!(g.status, GateStatus::Pass, "{:?}: {}", g.gate, g.summary);
    }
    let s = &gate(&c, ObligationId::ConformanceDifferential).summary;
    assert!(s.contains("25 public fixtures"), "{s}");
    assert!(s.contains("3 judge-sampled"), "{s}");
    assert!(s.contains("PUBLIC sampling seeds"), "{s}");
    let a = run(&f, &JobSpec::Adversarial(job.clone())).unwrap();
    assert_eq!(
        a.gates[0].status,
        GateStatus::Pass,
        "{}",
        a.gates[0].summary
    );
    let b = run(&f, &JobSpec::Benchmark(job)).unwrap();
    assert_eq!(
        b.gates[0].status,
        GateStatus::Pass,
        "{}",
        b.gates[0].summary
    );
}

/// Wrong-version inputs are refused before any candidate code runs: the v2
/// challenge re-pointed at the v1 fixture set (v1 requests/claims) and at the
/// v1 generator specs fails closed as infrastructure.
#[test]
fn v2_pipeline_rejects_v1_inputs() {
    let Some(Env { f, nearspec }) = v2_env() else {
        return;
    };
    let job = built(&f, &nearspec);
    let v1: ChallengeDefinition = serde_json::from_slice(
        &std::fs::read(repo().join("challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json"))
            .unwrap(),
    )
    .unwrap();
    // v1 fixtures under a v2 challenge.
    let mut j = job.clone();
    j.challenge.workload_suite.public_fixtures = v1.workload_suite.public_fixtures.clone();
    let e = run(&f, &JobSpec::Conformance(j)).unwrap_err();
    let m = e.to_string();
    assert!(matches!(e, ExecError::Infra(_)), "{m}");
    assert!(
        m.contains("near-arena-request-v1") && m.contains("near-arena-request-v2"),
        "{m}"
    );
    // v1 generator specs under a v2 challenge.
    let mut j = job.clone();
    for (c, c1) in j
        .challenge
        .workload_suite
        .classes
        .iter_mut()
        .zip(&v1.workload_suite.classes)
    {
        c.generator = c1.generator.clone();
    }
    let e = run(&f, &JobSpec::Conformance(j)).unwrap_err();
    assert!(e.to_string().contains("--scope v1"), "{e}");
    // A v3 encoding has no oracle: UNKNOWN, never PASS.
    let mut j = job;
    j.challenge.claim_encoding.format = "near-arena-claim-v3".into();
    let c = run(&f, &JobSpec::Conformance(j)).unwrap();
    assert!(c.gates.iter().all(|g| g.status == GateStatus::Unknown));
}
