//! Helpers shared by the stages that run entry points.

use crate::executor::{describe_exit, entry_spec, failure_reason, ExecError, JobRun, MAX_BUNDLE_BYTES};
use crate::jobs::{BuildOutputs, RunLimits};
use crate::oracle::Case;
use arena_sandbox::{ExitStatus, SandboxOutcome};
use arena_types::candidate::EntrySection as EntryPoints;
use arena_types::{ObligationId, ReasonCode};
use std::path::{Path, PathBuf};

/// Fetch and safely unpack the build bundle (bound to `build.bundle` by
/// TreeDigest); check the entry points are executable regular files in it.
pub fn fetch_bundle(r: &mut JobRun<'_>, build: &BuildOutputs, entry: &EntryPoints) -> Result<PathBuf, ExecError> {
    let archive = build.bundle_archive.as_ref().ok_or_else(|| ExecError::Infra("build outputs carry no bundle_archive".into()))?;
    let x = r.fetch_tree(archive, &build.bundle, MAX_BUNDLE_BYTES, "bundle")?;
    for (e, want) in [(&entry.prepare, &build.prepare), (&entry.prove, &build.prove), (&entry.verify, &build.verify)] {
        match x.tree.files.get(e.as_str()) {
            Some(f) if f.mode == arena_archive::FileMode::Exec && &f.digest == want => {}
            _ => return Err(ExecError::Infra(format!("bundle lacks executable {e:?} with the built digest {want}"))),
        }
    }
    Ok(x.root)
}

/// Fetch the frozen judge-run `public_dir` (bound by TreeDigest).
pub fn fetch_public(r: &mut JobRun<'_>, build: &BuildOutputs, limits: &RunLimits) -> Result<PathBuf, ExecError> {
    let archive = build.public_archive.as_ref().ok_or_else(|| ExecError::Infra("build outputs carry no public_archive".into()))?;
    let x = r.fetch_tree(archive, &build.public_artifacts, limits.max_public_artifact_bytes.clamp(1, MAX_BUNDLE_BYTES), "public")?;
    Ok(x.root)
}

pub struct Prepared {
    pub public_dir: PathBuf,
    pub tree: arena_archive::Tree,
    pub outcome: SandboxOutcome,
}

/// Judge-run `prepare --params <approved_params.bin> --out <public_dir>`.
/// v1 challenges carry no parameter blob: `approved_params.bin` is empty.
pub fn run_prepare(r: &mut JobRun<'_>, bundle: &Path, entry: &EntryPoints, limits: &RunLimits) -> Result<Result<Prepared, StepFailure>, ExecError> {
    let params_file = r.write_file(b"", "params")?;
    let out_dir = r.fresh("prepare-out");
    let layout = r.ctx.sandbox.layout();
    let mut spec = entry_spec(
        &layout,
        bundle,
        &entry.prepare,
        &["--params", "@in/params.bin", "--out", "@scratch/out/public"],
        &[(&params_file, "params.bin")],
        limits.max_prepare_ms,
        limits,
    );
    spec.env.push(("ARENA_STAGE".into(), "prepare".into()));
    if layout.flexible_scratch {
        spec.scratch_dirs.push("out/public".into());
    }
    spec.collect.push("out".into());
    spec.out_dir = Some(out_dir.clone());
    spec.max_output_bytes = limits.max_public_artifact_bytes;
    let o = r.run(&spec)?;
    if !o.exit.success() {
        let reason = failure_reason(&o);
        let gate = if reason == ReasonCode::ResourceLimit || reason == ReasonCode::Timeout { ObligationId::ResourceLimits } else { ObligationId::ProverReliability };
        return Ok(Err(fail(gate, reason, format!("prepare failed: {}", describe_exit(&o)))));
    }
    if let Some(e) = &o.output_error {
        return Ok(Err(if e.contains("size limit") {
            fail(ObligationId::ResourceLimits, ReasonCode::ResourceLimit, format!("public dir exceeds {} bytes", limits.max_public_artifact_bytes))
        } else {
            fail(ObligationId::ProverReliability, ReasonCode::ProverFailed, format!("prepare produced unusable output: {e}"))
        }));
    }
    let public_dir = out_dir.join("out/public");
    std::fs::create_dir_all(&public_dir)?;
    let tree = arena_archive::tree_from_dir(&public_dir, &arena_archive::Limits::default())?;
    Ok(Ok(Prepared { public_dir, tree, outcome: o }))
}

pub struct Proved {
    pub claim: Vec<u8>,
    pub proof: Vec<u8>,
    pub claim_path: PathBuf,
    pub proof_path: PathBuf,
    pub outcome: SandboxOutcome,
}

/// Why a prove/verify step did not produce a usable result.
#[derive(Debug)]
pub struct StepFailure {
    pub reason: ReasonCode,
    /// Which gate the failure belongs to.
    pub gate: arena_types::ObligationId,
    pub detail: String,
}

fn fail(gate: arena_types::ObligationId, reason: ReasonCode, detail: String) -> StepFailure {
    StepFailure { reason, gate, detail }
}

/// `prove` in a sandbox that holds the witness. Checks claim size and bytes
/// against the oracle's expected claim, and the proof size cap.
/// What `prove` / `verify` run against.
pub struct EntryEnv<'p> {
    pub bundle: &'p std::path::Path,
    pub entry: &'p EntryPoints,
    pub public_dir: &'p std::path::Path,
    pub limits: &'p RunLimits,
    pub cpu_set: Option<Vec<u32>>,
}

pub fn run_prove(r: &mut JobRun<'_>, env: &EntryEnv<'_>, case: &Case) -> Result<Result<Proved, StepFailure>, ExecError> {
    let request = r.write_file(&case.request, "request")?;
    let witness = r.write_file(&case.witness, "witness")?;
    let (request, witness) = (request.as_path(), witness.as_path());
    use ObligationId::*;
    let (bundle, entry, public_dir, limits) = (env.bundle, env.entry, env.public_dir, env.limits);
    let out_dir = r.fresh("prove-out");
    let layout = r.ctx.sandbox.layout();
    let mut spec = entry_spec(
        &layout,
        bundle,
        &entry.prove,
        &[
            "--public", "@in/public", "--request", "@in/request.bin", "--witness", "@in/witness.bin", "--claim-out",
            "@scratch/out/claim.bin", "--proof-out", "@scratch/out/proof.bin",
        ],
        &[(public_dir, "public"), (request, "request.bin"), (witness, "witness.bin")],
        limits.max_prove_ms,
        limits,
    );
    spec.env.push(("ARENA_STAGE".into(), "prove".into()));
    spec.cpu_set = env.cpu_set.clone();
    if layout.flexible_scratch {
        spec.scratch_dirs.push("out".into());
    }
    spec.collect = vec!["out".into()];
    spec.out_dir = Some(out_dir.clone());
    spec.max_output_bytes = limits.max_claim_bytes.saturating_add(limits.max_proof_bytes).saturating_add(1);
    let o = r.run(&spec)?;
    if !o.exit.success() {
        let reason = failure_reason(&o);
        let gate = if reason == ReasonCode::ResourceLimit { ResourceLimits } else { ProverReliability };
        return Ok(Err(fail(gate, reason, format!("prove {}", describe_exit(&o)))));
    }
    if let Some(e) = &o.output_error {
        return Ok(Err(if e.contains("size limit") {
            fail(ResourceLimits, ReasonCode::ResourceLimit, "claim+proof exceed size caps".into())
        } else {
            fail(ProverReliability, ReasonCode::ProverFailed, format!("unusable outputs: {e}"))
        }));
    }
    if o.peak_rss_bytes > limits.max_ram_bytes {
        return Ok(Err(fail(ResourceLimits, ReasonCode::ResourceLimit, format!("peak memory {} > {}", o.peak_rss_bytes, limits.max_ram_bytes))));
    }
    let claim_path = out_dir.join("out/claim.bin");
    let proof_path = out_dir.join("out/proof.bin");
    let (Ok(claim), Ok(proof)) = (std::fs::read(&claim_path), std::fs::read(&proof_path)) else {
        return Ok(Err(fail(ProverReliability, ReasonCode::ProverFailed, "prove exited 0 without claim.bin and proof.bin".into())));
    };
    if claim.len() as u64 > limits.max_claim_bytes {
        return Ok(Err(fail(ConformanceDifferential, ReasonCode::ClaimMismatch, format!("claim is {} bytes > max_claim_bytes", claim.len()))));
    }
    if claim != case.expected_claim {
        return Ok(Err(fail(ConformanceDifferential, ReasonCode::ClaimMismatch, "claim.bin differs from the oracle's expected claim".into())));
    }
    if proof.len() as u64 > limits.max_proof_bytes {
        return Ok(Err(fail(ResourceLimits, ReasonCode::ResourceLimit, format!("proof is {} bytes > max_proof_bytes {}", proof.len(), limits.max_proof_bytes))));
    }
    Ok(Ok(Proved { claim, proof, claim_path, proof_path, outcome: o }))
}

/// Verifier verdict (CONTRACTS §4: 0 accept, 1 reject, anything else error).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Accept,
    Reject,
    /// Crash, other exit code, signal, OOM: never acceptance.
    Error,
    TimedOut,
}

/// `verify` in a SEPARATE sandbox that receives only the bundle, the public
/// dir, the claim and the proof — no witness, no oracle, no expected result.
pub fn run_verify(
    r: &mut JobRun<'_>,
    env: &EntryEnv<'_>,
    claim: &std::path::Path,
    proof: &std::path::Path,
) -> Result<(Verdict, SandboxOutcome), ExecError> {
    let (bundle, entry, public_dir, limits) = (env.bundle, env.entry, env.public_dir, env.limits);
    let layout = r.ctx.sandbox.layout();
    let mut spec = entry_spec(
        &layout,
        bundle,
        &entry.verify,
        &["--public", "@in/public", "--claim", "@in/claim.bin", "--proof", "@in/proof.bin"],
        &[(public_dir, "public"), (claim, "claim.bin"), (proof, "proof.bin")],
        limits.max_verify_ms,
        limits,
    );
    spec.env.push(("ARENA_STAGE".into(), "verify".into()));
    spec.cpu_set = env.cpu_set.clone();
    let o = r.run(&spec)?;
    let v = match o.exit {
        ExitStatus::Exited(0) => Verdict::Accept,
        ExitStatus::Exited(1) => Verdict::Reject,
        ExitStatus::TimedOut => Verdict::TimedOut,
        _ => Verdict::Error,
    };
    Ok((v, o))
}

/// Label a case for summaries without leaking held-out ids.
pub fn case_label(id: &str, public: bool) -> String {
    if public {
        format!("case {id:?}")
    } else {
        "a held-out case".to_string()
    }
}
