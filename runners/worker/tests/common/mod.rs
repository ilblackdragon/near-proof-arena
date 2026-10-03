//! Shared fixtures: a toy candidate written in POSIX sh (sha256sum-based
//! "proofs"), a directory artifact store, and a bwrap-dev executor that uses
//! the `arena-worker` binary itself as the sandbox helper.
#![allow(dead_code)]

use arena_sandbox::{BwrapConfig, BwrapDev, HelperCommand};
use arena_types::Digest;
use arena_worker::executor::{BuildEnv, StageExecutor, WorkerContext};
use arena_worker::jobs::*;
use arena_worker::mutators::MutatorRegistry;
use arena_worker::store::{ArtifactStore, FsStore};
use std::collections::BTreeMap;
use std::sync::Arc;

pub const CHALLENGE: &str = "chl_0123456789abcdef0123456789abcdef";

pub const MANIFEST: &str = r#"
schema = "arena-candidate-v1"
name = "toy-sha"
agent = "test"
challenge = "chl_0123456789abcdef0123456789abcdef"
backend_family = "toy"
security_profile_request = "validity-classical-128"
hardware = { gpu = false, min_ram_gb = 1 }
[build]
recipe = "build-recipe/build.sh"
outputs = ["out"]
[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"
"#;

pub const BUILD: &str = r#"#!/bin/sh
set -e
mkdir -p out
for f in prepare prove verify; do cp source/$f.sh out/$f; chmod 755 out/$f; done
"#;

pub const PREPARE: &str = r#"#!/bin/sh
set -e
while [ $# -gt 0 ]; do case "$1" in --params) params=$2; shift 2;; --out) out=$2; shift 2;; *) exit 2;; esac; done
mkdir -p "$out"
{ printf 'toy-key-v1:'; sha256sum < "$params" | cut -d' ' -f1; } > "$out/key"
"#;

pub const PROVE: &str = r#"#!/bin/sh
set -e
while [ $# -gt 0 ]; do case "$1" in
  --public) pub=$2; shift 2;; --request) req=$2; shift 2;; --witness) wit=$2; shift 2;;
  --claim-out) claim=$2; shift 2;; --proof-out) proof=$2; shift 2;; *) exit 2;; esac; done
test -r "$wit"
printf 'CLAIM:%s' "$(sha256sum < "$req" | cut -d' ' -f1)" > "$claim"
printf 'PROOF:%s' "$(cat "$claim" "$pub/key" | sha256sum | cut -d' ' -f1)" > "$proof"
"#;

pub const VERIFY: &str = r#"#!/bin/sh
while [ $# -gt 0 ]; do case "$1" in
  --public) pub=$2; shift 2;; --claim) claim=$2; shift 2;; --proof) proof=$2; shift 2;; *) exit 2;; esac; done
# The verify sandbox must never see the witness or the request.
for p in /in /arena/in; do
  if [ -e $p/witness.bin ] || [ -e $p/request.bin ]; then echo "SAW PRIVATE INPUT" >&2; exit 3; fi
done
printf 'PROOF:%s' "$(cat "$claim" "$pub/key" | sha256sum | cut -d' ' -f1)" > ./expected
cmp -s ./expected "$proof" && exit 0
exit 1
"#;

/// Honest toy claim for a request.
pub fn claim_for(request: &[u8]) -> Vec<u8> {
    format!("CLAIM:{}", Digest::of_bytes(request).hex()).into_bytes()
}

pub fn package_files() -> BTreeMap<String, (u32, Vec<u8>)> {
    let mut m = BTreeMap::new();
    m.insert("candidate.toml".to_string(), (0o644, MANIFEST.as_bytes().to_vec()));
    m.insert("README.md".to_string(), (0o644, b"toy".to_vec()));
    m.insert("dependency-locks/none".to_string(), (0o644, vec![]));
    m.insert("build-recipe/build.sh".to_string(), (0o755, BUILD.as_bytes().to_vec()));
    m.insert("source/prepare.sh".to_string(), (0o644, PREPARE.as_bytes().to_vec()));
    m.insert("source/prove.sh".to_string(), (0o644, PROVE.as_bytes().to_vec()));
    m.insert("source/verify.sh".to_string(), (0o644, VERIFY.as_bytes().to_vec()));
    m
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
}

pub fn fixture() -> Fixture {
    assert_eq!(std::env::var("ARENA_DEV_UNSAFE").as_deref(), Ok("1"), "worker tests need ARENA_DEV_UNSAFE=1 (bwrap-dev)");
    let tmp = tempfile::tempdir().unwrap();
    let store = Arc::new(FsStore::new(tmp.path().join("store")).unwrap());
    let helper = HelperCommand { exe: env!("CARGO_BIN_EXE_arena-worker").into(), prefix_args: vec![arena_worker::HELPER_ARG.into()] };
    let sb = BwrapDev::new(BwrapConfig::new(helper, tmp.path().join("sandbox"))).unwrap();
    let ctx = WorkerContext {
        worker_id: "test-worker".into(),
        sandbox: Arc::new(sb),
        store: store.clone(),
        work_root: tmp.path().join("jobs"),
        build: BuildEnv::default(),
        bench_cpus: None,
        mutators: MutatorRegistry::with_adversarial_lane(),
        keep_workdirs: false,
    };
    Fixture { tmp, store, exec: StageExecutor::new(ctx) }
}

pub fn job(id: &str, spec: JobSpec) -> Job {
    Job { id: id.into(), submission_id: "sub_test".into(), attempt: 1, lease_until: "2099-01-01T00:00:00Z".into(), spec }
}

pub fn run_limits() -> RunLimits {
    RunLimits {
        max_prepare_ms: 20_000,
        max_prove_ms: 20_000,
        max_verify_ms: 20_000,
        max_ram_bytes: 256 << 20,
        max_proof_bytes: 4096,
        max_claim_bytes: 1024,
        max_request_bytes: 1 << 20,
        max_witness_bytes: 1 << 20,
        max_public_artifact_bytes: 1 << 20,
        max_pids: 64,
        scratch_mb: 16,
    }
}

pub fn build_limits() -> BuildLimits {
    BuildLimits { max_build_ms: 30_000, mem_bytes: 256 << 20, pids: 64, scratch_mb: 32, max_output_bytes: 16 << 20 }
}

pub fn entry() -> EntryPoints {
    EntryPoints { prepare: "out/prepare".into(), prove: "out/prove".into(), verify: "out/verify".into() }
}

impl Fixture {
    pub fn put(&self, b: &[u8]) -> Digest {
        self.store.put(b).unwrap()
    }

    /// Oracle cases: (request, witness, expected claim) in the store.
    pub fn cases(&self, n: usize, public: bool, claim: impl Fn(&[u8]) -> Vec<u8>) -> Vec<OracleCase> {
        (0..n)
            .map(|i| {
                let req = format!("request-{i}-{public}").into_bytes();
                OracleCase {
                    id: format!("{}-{i}", if public { "pub" } else { "heldout-secret" }),
                    request: self.put(&req),
                    witness: self.put(format!("witness-{i}").as_bytes()),
                    expected_claim: self.put(&claim(&req)),
                    public,
                }
            })
            .collect()
    }

    /// Validate + build a package; returns the bundle digest.
    pub fn build(&self, files: &BTreeMap<String, (u32, Vec<u8>)>) -> (JobOutput, Option<Digest>) {
        use arena_worker::executor::JobExecutor;
        let pkg = self.put(&tar_of(files));
        let out = self
            .exec
            .execute(
                &job("build", JobSpec::Build(BuildJob { package: pkg, toolchain_image: None, limits: build_limits(), source_date_epoch: 0 })),
                &std::sync::atomic::AtomicBool::new(false),
            )
            .unwrap();
        let bundle = out.artifact("bundle").cloned();
        (out, bundle)
    }
}
