//! Helpers shared by the stages that run entry points.

use crate::executor::{describe_exit, entry_spec, failure_reason, ExecError, JobRun, MAX_BUNDLE_BYTES};
use crate::gate::Gate;
use crate::jobs::{EntryPoints, RunLimits};
use arena_sandbox::{ExitStatus, SandboxOutcome};
use arena_types::{Digest, ReasonCode};
use std::path::PathBuf;

/// Fetch and safely unpack the build bundle; check the entry points are
/// executable regular files in it.
pub fn fetch_bundle(r: &mut JobRun<'_>, bundle: &Digest, entry: &EntryPoints) -> Result<PathBuf, ExecError> {
    let x = r.fetch_tree(bundle, MAX_BUNDLE_BYTES, "bundle")?;
    for e in [&entry.prepare, &entry.prove, &entry.verify] {
        if !x.tree.is_exec(e) {
            return Err(ExecError::Infra(format!("bundle {bundle} lacks executable {e:?} (build stage should have caught this)")));
        }
    }
    Ok(x.root)
}

pub struct Prepared {
    pub public_dir: PathBuf,
    pub tree: arena_archive::Tree,
    pub outcome: SandboxOutcome,
}

/// Judge-run `prepare --params <p> --out <public_dir>`. Failures are
/// recorded on `reliability` / `resources`; `Ok(None)` means it failed.
pub fn run_prepare(
    r: &mut JobRun<'_>,
    bundle: &std::path::Path,
    entry: &EntryPoints,
    params: &Digest,
    limits: &RunLimits,
    reliability: &mut Gate,
    resources: &mut Gate,
) -> Result<Option<Prepared>, ExecError> {
    let params_file = r.fetch_file(params, 1 << 30, "params")?;
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
        if matches!(o.exit, ExitStatus::TimedOut | ExitStatus::OomKilled) {
            resources.fail(ReasonCode::ResourceLimit, format!("prepare {}", describe_exit(&o)));
        }
        reliability.fail(reason, format!("prepare failed: {}", describe_exit(&o)));
        return Ok(None);
    }
    if let Some(e) = &o.output_error {
        if e.contains("size limit") {
            resources.fail(ReasonCode::ResourceLimit, format!("public dir exceeds {} bytes", limits.max_public_artifact_bytes));
        } else {
            reliability.fail(ReasonCode::ProverFailed, format!("prepare produced unusable output: {e}"));
        }
        return Ok(None);
    }
    let public_dir = out_dir.join("out/public");
    std::fs::create_dir_all(&public_dir)?;
    let tree = arena_archive::tree_from_dir(&public_dir, &arena_archive::Limits::default())?;
    Ok(Some(Prepared { public_dir, tree, outcome: o }))
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

impl StepFailure {
    /// Summary text for a case. On a held-out case `prove` has seen the secret
    /// request/witness, and much of `detail` is chosen by the candidate:
    /// output file names quoted in collect errors, exit codes, proof/claim
    /// sizes, peak memory. All of that would be a covert channel into the
    /// public gate summary. Held-out failures therefore report only the fixed
    /// reason code.
    pub fn detail_for(&self, public: bool) -> String {
        if public {
            self.detail.clone()
        } else {
            format!("failed ({:?}; details withheld for held-out cases)", self.reason)
        }
    }
}

/// `describe_exit` for summaries: exit codes and signals are candidate-chosen,
/// so they are withheld on held-out cases (see [`StepFailure::detail_for`]).
pub fn exit_for(o: &arena_sandbox::SandboxOutcome, public: bool) -> String {
    if public {
        crate::executor::describe_exit(o)
    } else {
        "details withheld for held-out cases".into()
    }
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

pub fn run_prove(
    r: &mut JobRun<'_>,
    env: &EntryEnv<'_>,
    request: &std::path::Path,
    witness: &std::path::Path,
    expected_claim: &Digest,
) -> Result<Result<Proved, StepFailure>, ExecError> {
    use arena_types::ObligationId::*;
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
    if &Digest::of_bytes(&claim) != expected_claim {
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
