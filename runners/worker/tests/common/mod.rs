//! Shared fixtures: the toy reference candidate (`tests/e2e/toy-candidate`,
//! C, built with `cc` inside the sandbox) against the signed demo challenge
//! (`challenges/chl_54c65fe7c73c5abcfe500681889177bc.json`), a directory
//! artifact store, and a bwrap-dev executor that uses the `arena-worker`
//! binary itself as the sandbox helper.
#![allow(dead_code)]

use arena_jobs::*;
use arena_sandbox::{BwrapConfig, BwrapDev, HelperCommand, Sandbox};
use arena_types::{
    CandidateManifest, ChallengeDefinition, Digest, GateResult, GateStatus, ObligationId,
    ReasonCode,
};
use arena_worker::executor::{BuildEnv, JobExecutor, StageExecutor, WorkerContext};
use arena_worker::mutators::MutatorRegistry;
use arena_worker::oracle::Oracles;
use arena_worker::store::{ArtifactStore, FsStore};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

pub const CHALLENGE: &str = "chl_54c65fe7c73c5abcfe500681889177bc";

pub fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

pub fn challenge() -> ChallengeDefinition {
    serde_json::from_slice(
        &std::fs::read(repo().join(format!("challenges/{CHALLENGE}.json"))).unwrap(),
    )
    .unwrap()
}

/// The toy candidate's files (path -> (mode, bytes)).
pub fn package_files() -> BTreeMap<String, (u32, Vec<u8>)> {
    let root = repo().join("tests/e2e/toy-candidate");
    let t = arena_archive::tree_from_dir(&root, &arena_archive::Limits::default()).unwrap();
    t.files
        .iter()
        .map(|(p, f)| {
            (
                p.clone(),
                (
                    if f.mode == arena_archive::FileMode::Exec {
                        0o755
                    } else {
                        0o644
                    },
                    std::fs::read(root.join(p)).unwrap(),
                ),
            )
        })
        .collect()
}

pub fn set(files: &mut BTreeMap<String, (u32, Vec<u8>)>, path: &str, content: &str) {
    let mode = files.get(path).map(|f| f.0).unwrap_or(0o644);
    files.insert(path.to_string(), (mode, content.as_bytes().to_vec()));
}

pub fn tar_of(files: &BTreeMap<String, (u32, Vec<u8>)>) -> Vec<u8> {
    let mut b = tar::Builder::new(Vec::new());
    for (p, (mode, data)) in files {
        let mut h = tar::Header::new_gnu();
        h.set_size(data.len() as u64);
        h.set_mode(*mode);
        h.set_mtime(0);
        b.append_data(&mut h, p, &data[..]).unwrap();
    }
    zstd::encode_all(&b.into_inner().unwrap()[..], 3).unwrap()
}

pub struct Fixture {
    pub tmp: tempfile::TempDir,
    pub store: Arc<FsStore>,
    pub exec: StageExecutor,
    pub chal: ChallengeDefinition,
}

pub fn executor(sandbox: Arc<dyn Sandbox>, store: Arc<FsStore>, work: &Path) -> StageExecutor {
    let mut oracles = Oracles::builtin();
    oracles
        .add_fixtures_dir(&repo().join("challenges/demo/toy-arithmetic/fixtures"))
        .unwrap();
    StageExecutor::new(WorkerContext {
        worker_id: "test-worker".into(),
        sandbox,
        store,
        work_root: work.to_path_buf(),
        build: BuildEnv::default(),
        bench_cpus: None,
        run_cpus: None,
        bench_batch_cap: Some(2),
        conformance_samples: 4,
        mutators: MutatorRegistry::with_adversarial_lane(),
        oracles,
        formal: None,
        npai_verify: None,
        interp_ref: None,
        calibration_bin: None,
        keep_workdirs: false,
    })
}

pub fn fixture() -> Fixture {
    assert_eq!(
        std::env::var("ARENA_DEV_UNSAFE").as_deref(),
        Ok("1"),
        "worker tests need ARENA_DEV_UNSAFE=1 (bwrap-dev)"
    );
    let tmp = tempfile::tempdir().unwrap();
    let store = Arc::new(FsStore::new(tmp.path().join("store")).unwrap());
    let helper = HelperCommand {
        exe: env!("CARGO_BIN_EXE_arena-worker").into(),
        prefix_args: vec![arena_worker::HELPER_ARG.into()],
    };
    let sb = BwrapDev::new(BwrapConfig::new(helper, tmp.path().join("sandbox"))).unwrap();
    let exec = executor(Arc::new(sb), store.clone(), &tmp.path().join("jobs"));
    Fixture {
        tmp,
        store,
        exec,
        chal: challenge(),
    }
}

impl Fixture {
    pub fn put(&self, b: &[u8]) -> Digest {
        self.store.put(b).unwrap()
    }

    pub fn ctx(&self, package: &Digest) -> JobContext {
        JobContext {
            submission_id: "sub_test".into(),
            run_id: "run_test".into(),
            challenge_id: CHALLENGE.into(),
            challenge_digest: self.chal.digest().unwrap(),
            tier: self.chal.tier,
            package_digest: package.clone(),
        }
    }

    pub fn exec(&self, spec: JobSpec) -> JobResult {
        self.exec
            .execute(&spec, "t", &AtomicBool::new(false))
            .unwrap()
    }

    pub fn validate(&self, files: &BTreeMap<String, (u32, Vec<u8>)>) -> (JobResult, Digest) {
        let pkg = self.put(&tar_of(files));
        (
            self.exec(JobSpec::Validate(ValidateJob {
                ctx: self.ctx(&pkg),
                challenge: self.chal.clone(),
            })),
            pkg,
        )
    }

    /// Validate + build; returns the build result and (manifest, outputs) when it passed.
    pub fn build(
        &self,
        files: &BTreeMap<String, (u32, Vec<u8>)>,
    ) -> (JobResult, Option<(Digest, CandidateManifest, BuildOutputs)>) {
        let (v, pkg) = self.validate(files);
        assert_pass(&v, ObligationId::PkgWellformed);
        let manifest = v.manifest.clone().unwrap();
        let b = self.exec(JobSpec::Build(BuildJob {
            ctx: self.ctx(&pkg),
            challenge: self.chal.clone(),
            manifest: manifest.clone(),
        }));
        let out = b
            .build
            .clone()
            .filter(|_| gate(&b, ObligationId::BuildReproducible).status == GateStatus::Pass)
            .map(|o| (pkg, manifest, o));
        (b, out)
    }

    pub fn exec_job(
        &self,
        pkg: &Digest,
        manifest: &CandidateManifest,
        build: &BuildOutputs,
    ) -> ExecJob {
        ExecJob {
            ctx: self.ctx(pkg),
            challenge: self.chal.clone(),
            manifest: manifest.clone(),
            build: build.clone(),
            reference: None,
        }
    }
}

pub fn gate(o: &JobResult, g: ObligationId) -> &GateResult {
    o.gates
        .iter()
        .find(|x| x.gate == g)
        .unwrap_or_else(|| panic!("no {g:?} gate in {:?}", o.gates))
}

pub fn assert_pass(o: &JobResult, g: ObligationId) {
    let r = gate(o, g);
    assert_eq!(
        r.status,
        GateStatus::Pass,
        "{g:?}: {} {:?}",
        r.summary,
        r.reason_codes
    );
}

pub fn assert_fail(o: &JobResult, g: ObligationId, reason: ReasonCode) {
    let r = gate(o, g);
    assert_eq!(r.status, GateStatus::Fail, "{g:?}: {}", r.summary);
    assert!(
        r.reason_codes.contains(&reason),
        "{g:?}: {:?} lacks {reason:?}; {}",
        r.reason_codes,
        r.summary
    );
}

/// The commit whose `formal-core/` + `spec/lean/` the NEAR v1 family
/// (`chl_5ef2…`, v1-1, v1-2, v1-3, experimental `chl_b7c8…`) pins
/// (`formal_spec.tree_digest = sha256:8090432a…`).
pub const NEAR_V1_TRUSTED_COMMIT: &str = "6873c9980fd93c0483e93b94fe7e8a1fe0d52d52";

/// Extract the tracked `formal-core/` + `spec/lean/` of `commit` into `dest`
/// (`None` if the commit is not in this clone, e.g. a shallow CI checkout).
pub fn extract_trusted(commit: &str, dest: &Path) -> Option<()> {
    let ok = std::process::Command::new("git")
        .arg("-C")
        .arg(repo())
        .args(["cat-file", "-e", &format!("{commit}^{{commit}}")])
        .status()
        .ok()?
        .success();
    if !ok {
        return None;
    }
    std::fs::create_dir_all(dest).unwrap();
    let st = std::process::Command::new("sh")
        .arg("-c")
        .arg(format!(
            "git -C \"$1\" archive --format=tar {commit} -- formal-core spec/lean | tar -x -C \"$2\""
        ))
        .arg("sh")
        .arg(repo())
        .arg(dest)
        .status()
        .unwrap();
    assert!(st.success(), "git archive {commit}");
    Some(())
}

/// A trusted-tree store holding the frozen tree `chal` pins, frozen from
/// `commit` (and checked to hash to the pin). `None` when the commit is
/// unavailable.
pub fn frozen_store(tmp: &Path, chal: &ChallengeDefinition, commit: &str) -> Option<PathBuf> {
    let store = tmp.join("trusted-trees");
    let pin = &chal.semantic_scope.formal_spec.tree_digest;
    let dir = arena_types::trusted_tree::entry_dir(&store, pin);
    if !dir.exists() {
        extract_trusted(commit, &dir)?;
    }
    assert_eq!(
        &arena_types::trusted_tree::digest_of(&dir).unwrap(),
        pin,
        "{commit} is not the commit {} pins",
        chal.semantic_scope.name
    );
    Some(store)
}

// --------------------------------------------------------------------------
// Env-gated test skips (CI convention, see .github/workflows/ci.yml).
// --------------------------------------------------------------------------

/// Report that the current test did not exercise what it gates on. Prints one
/// `ARENA-TEST-SKIPPED: <test>: <reason>` line to stderr, or panics when
/// `ARENA_REQUIRE_GATED_TESTS=1` (a CI job that claims to run the gated tests
/// must fail rather than report a skipped test as passed). The caller still
/// returns early itself; prefer the [`skip_gated!`] macro, which fills in the
/// test name.
pub fn report_gated_skip(test: &str, reason: &str) {
    let line = format!("ARENA-TEST-SKIPPED: {test}: {reason}");
    if std::env::var("ARENA_REQUIRE_GATED_TESTS").as_deref() == Ok("1") {
        panic!("{line} (ARENA_REQUIRE_GATED_TESTS=1: gated tests must run, not skip)");
    }
    eprintln!("{line}");
}

/// `skip_gated!("reason {}", x)`: [`report_gated_skip`] with the enclosing
/// function's path (e.g. `near::reexec_witness_reference_all_stages`).
#[allow(unused_macros)]
macro_rules! skip_gated {
    ($($reason:tt)+) => {{
        fn __arena_here() {}
        let name = ::std::any::type_name_of_val(&__arena_here);
        let name = name.strip_suffix("::__arena_here").unwrap_or(name);
        $crate::common::report_gated_skip(name, &format!($($reason)+));
    }};
}
#[allow(unused_imports)]
pub(crate) use skip_gated;
