//! Helpers shared by the stages that run entry points.

use crate::executor::{
    describe_exit, entry_spec, failure_reason, ExecError, JobRun, MAX_BUNDLE_BYTES,
};
use crate::gate::Gate;
use crate::jobs::{EntryPoints, RunLimits};
use arena_sandbox::{ExitStatus, SandboxOutcome};
use arena_types::{Digest, ReasonCode};
use std::path::PathBuf;

/// Fail-closed protocol-version check of one oracle request
/// ([`RequestPin`](crate::jobs::RequestPin)): a mismatch is a judge-side
/// error, so the job fails as infra and nothing is attributed to the
/// candidate. Held-out case ids are not echoed.
pub fn check_request_pin(
    pin: &crate::jobs::RequestPin,
    request: &[u8],
    case_id: &str,
    public: bool,
) -> Result<(), ExecError> {
    pin.check(request).map_err(|e| {
        ExecError::Infra(format!(
            "fail-closed: oracle request {} rejected: {e}",
            case_label(case_id, public)
        ))
    })
}

/// Fetch and safely unpack the build bundle; check the entry points are
/// executable regular files in it.
pub fn fetch_bundle(
    r: &mut JobRun<'_>,
    bundle: &Digest,
    entry: &EntryPoints,
) -> Result<PathBuf, ExecError> {
    let x = r.fetch_tree(bundle, MAX_BUNDLE_BYTES, "bundle")?;
    for e in [&entry.prepare, &entry.prove, &entry.verify] {
        if !x.tree.is_exec(e) {
            return Err(ExecError::Infra(format!(
                "bundle {bundle} lacks executable {e:?} (build stage should have caught this)"
            )));
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
            resources.fail(
                ReasonCode::ResourceLimit,
                format!("prepare {}", describe_exit(&o)),
            );
        }
        reliability.fail(reason, format!("prepare failed: {}", describe_exit(&o)));
        return Ok(None);
    }
    if let Some(e) = &o.output_error {
        if e.contains("size limit") {
            resources.fail(
                ReasonCode::ResourceLimit,
                format!(
                    "public dir exceeds {} bytes",
                    limits.max_public_artifact_bytes
                ),
            );
        } else {
            reliability.fail(
                ReasonCode::ProverFailed,
                format!("prepare produced unusable output: {e}"),
            );
        }
        return Ok(None);
    }
    let public_dir = out_dir.join("out/public");
    std::fs::create_dir_all(&public_dir)?;
    let tree = arena_archive::tree_from_dir(&public_dir, &arena_archive::Limits::default())?;
    Ok(Some(Prepared {
        public_dir,
        tree,
        outcome: o,
    }))
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
    StepFailure {
        reason,
        gate,
        detail,
    }
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
            format!(
                "failed ({:?}; details withheld for held-out cases)",
                self.reason
            )
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

fn prove_spec(
    r: &mut JobRun<'_>,
    env: &EntryEnv<'_>,
    files: &[(&std::path::Path, &str)],
) -> arena_sandbox::SandboxSpec {
    let (bundle, entry, public_dir, limits) = (env.bundle, env.entry, env.public_dir, env.limits);
    let layout = r.ctx.sandbox.layout();
    let mut all: Vec<(&std::path::Path, &str)> = vec![(public_dir, "public")];
    all.extend_from_slice(files);
    let mut spec = entry_spec(
        &layout,
        bundle,
        &entry.prove,
        &[
            "--public",
            "@in/public",
            "--request",
            "@in/request.bin",
            "--witness",
            "@in/witness.bin",
            "--claim-out",
            "@scratch/out/claim.bin",
            "--proof-out",
            "@scratch/out/proof.bin",
        ],
        &all,
        limits.max_prove_ms,
        limits,
    );
    spec.env.push(("ARENA_STAGE".into(), "prove".into()));
    spec.cpu_set = env.cpu_set.clone();
    if layout.flexible_scratch {
        spec.scratch_dirs.push("out".into());
    }
    spec.collect = vec!["out".into()];
    spec.max_output_bytes = limits
        .max_claim_bytes
        .saturating_add(limits.max_proof_bytes)
        .saturating_add(1);
    spec
}

pub fn run_prove(
    r: &mut JobRun<'_>,
    env: &EntryEnv<'_>,
    request: &std::path::Path,
    witness: &std::path::Path,
    expected_claim: &Digest,
) -> Result<Result<Proved, StepFailure>, ExecError> {
    let out_dir = r.fresh("prove-out");
    let mut spec = prove_spec(
        r,
        env,
        &[(request, "request.bin"), (witness, "witness.bin")],
    );
    spec.out_dir = Some(out_dir.clone());
    let o = r.run(&spec)?;
    Ok(check_proved(o, &out_dir, expected_claim, env.limits))
}

/// One benchmark batch: every request proved by a fresh `prove` process with
/// a wiped scratch and only its own request/witness, all inside one sandbox
/// instance when the backend supports it ([`arena_sandbox::Sandbox::run_steps`];
/// Firecracker: one microVM per batch). Returns one result per case; the
/// batch stops at the first failed invocation (no partial credit).
pub fn run_prove_batch(
    r: &mut JobRun<'_>,
    env: &EntryEnv<'_>,
    cases: &[(PathBuf, PathBuf, Digest)],
) -> Result<Vec<Result<Proved, StepFailure>>, ExecError> {
    let base = prove_spec(r, env, &[]);
    let layout = r.ctx.sandbox.layout();
    let mut steps = Vec::with_capacity(cases.len());
    let mut dirs = Vec::with_capacity(cases.len());
    for (req, wit, _) in cases {
        let out_dir = r.fresh("prove-out");
        steps.push(arena_sandbox::StepSpec {
            argv: base.argv.clone(),
            ro_files: vec![
                arena_sandbox::Mount {
                    host: req.clone(),
                    guest: format!("{}/request.bin", layout.inputs),
                },
                arena_sandbox::Mount {
                    host: wit.clone(),
                    guest: format!("{}/witness.bin", layout.inputs),
                },
            ],
            collect: base.collect.clone(),
            out_dir: Some(out_dir.clone()),
            wall_timeout: base.wall_timeout,
        });
        dirs.push(out_dir);
    }
    let outs = r.run_steps(&base, &steps)?;
    if outs.is_empty() || outs.len() > cases.len() {
        return Err(ExecError::Infra(format!(
            "run_steps returned {} outcomes for {} steps",
            outs.len(),
            cases.len()
        )));
    }
    let mut res = Vec::with_capacity(outs.len());
    for (i, o) in outs.into_iter().enumerate() {
        let p = check_proved(o, &dirs[i], &cases[i].2, env.limits);
        let failed = p.is_err();
        res.push(p);
        if failed {
            break;
        }
    }
    if res.len() < cases.len() && res.last().is_some_and(|p| p.is_ok()) {
        return Err(ExecError::Infra(
            "sandbox stopped a batch after a successful step".into(),
        ));
    }
    Ok(res)
}

/// Checks one prove outcome: exit, outputs, memory, claim bytes against the
/// oracle's expected claim, claim/proof size caps.
pub fn check_proved(
    o: SandboxOutcome,
    out_dir: &std::path::Path,
    expected_claim: &Digest,
    limits: &RunLimits,
) -> Result<Proved, StepFailure> {
    use arena_types::ObligationId::*;
    if !o.exit.success() {
        let reason = failure_reason(&o);
        let gate = if reason == ReasonCode::ResourceLimit {
            ResourceLimits
        } else {
            ProverReliability
        };
        return Err(fail(gate, reason, format!("prove {}", describe_exit(&o))));
    }
    if let Some(e) = &o.output_error {
        return Err(if e.contains("size limit") {
            fail(
                ResourceLimits,
                ReasonCode::ResourceLimit,
                "claim+proof exceed size caps".into(),
            )
        } else {
            fail(
                ProverReliability,
                ReasonCode::ProverFailed,
                format!("unusable outputs: {e}"),
            )
        });
    }
    if o.peak_rss_bytes > limits.max_ram_bytes {
        return Err(fail(
            ResourceLimits,
            ReasonCode::ResourceLimit,
            format!(
                "peak memory {} > {}",
                o.peak_rss_bytes, limits.max_ram_bytes
            ),
        ));
    }
    let claim_path = out_dir.join("out/claim.bin");
    let proof_path = out_dir.join("out/proof.bin");
    let (Ok(claim), Ok(proof)) = (std::fs::read(&claim_path), std::fs::read(&proof_path)) else {
        return Err(fail(
            ProverReliability,
            ReasonCode::ProverFailed,
            "prove exited 0 without claim.bin and proof.bin".into(),
        ));
    };
    if claim.len() as u64 > limits.max_claim_bytes {
        return Err(fail(
            ConformanceDifferential,
            ReasonCode::ClaimMismatch,
            format!("claim is {} bytes > max_claim_bytes", claim.len()),
        ));
    }
    if &Digest::of_bytes(&claim) != expected_claim {
        return Err(fail(
            ConformanceDifferential,
            ReasonCode::ClaimMismatch,
            "claim.bin differs from the oracle's expected claim".into(),
        ));
    }
    if proof.len() as u64 > limits.max_proof_bytes {
        return Err(fail(
            ResourceLimits,
            ReasonCode::ResourceLimit,
            format!(
                "proof is {} bytes > max_proof_bytes {}",
                proof.len(),
                limits.max_proof_bytes
            ),
        ));
    }
    Ok(Proved {
        claim,
        proof,
        claim_path,
        proof_path,
        outcome: o,
    })
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
fn verify_spec(
    r: &mut JobRun<'_>,
    env: &EntryEnv<'_>,
    files: &[(&std::path::Path, &str)],
) -> arena_sandbox::SandboxSpec {
    let (bundle, entry, public_dir, limits) = (env.bundle, env.entry, env.public_dir, env.limits);
    let layout = r.ctx.sandbox.layout();
    let mut all: Vec<(&std::path::Path, &str)> = vec![(public_dir, "public")];
    all.extend_from_slice(files);
    let mut spec = entry_spec(
        &layout,
        bundle,
        &entry.verify,
        &[
            "--public",
            "@in/public",
            "--claim",
            "@in/claim.bin",
            "--proof",
            "@in/proof.bin",
        ],
        &all,
        limits.max_verify_ms,
        limits,
    );
    spec.env.push(("ARENA_STAGE".into(), "verify".into()));
    spec.cpu_set = env.cpu_set.clone();
    spec
}

fn verdict(o: &SandboxOutcome) -> Verdict {
    match o.exit {
        ExitStatus::Exited(0) => Verdict::Accept,
        ExitStatus::Exited(1) => Verdict::Reject,
        ExitStatus::TimedOut => Verdict::TimedOut,
        _ => Verdict::Error,
    }
}

pub fn run_verify(
    r: &mut JobRun<'_>,
    env: &EntryEnv<'_>,
    claim: &std::path::Path,
    proof: &std::path::Path,
) -> Result<(Verdict, SandboxOutcome), ExecError> {
    let spec = verify_spec(r, env, &[(claim, "claim.bin"), (proof, "proof.bin")]);
    let o = r.run(&spec)?;
    Ok((verdict(&o), o))
}

/// `verify` of a batch of (claim, proof) pairs, each a fresh process in a
/// fresh scratch seeing only its own pair; one sandbox instance per batch
/// when the backend supports it. Stops at the first non-accepting verdict.
pub fn run_verify_batch(
    r: &mut JobRun<'_>,
    env: &EntryEnv<'_>,
    pairs: &[(PathBuf, PathBuf)],
) -> Result<Vec<(Verdict, SandboxOutcome)>, ExecError> {
    let base = verify_spec(r, env, &[]);
    let layout = r.ctx.sandbox.layout();
    let steps: Vec<_> = pairs
        .iter()
        .map(|(c, p)| arena_sandbox::StepSpec {
            argv: base.argv.clone(),
            ro_files: vec![
                arena_sandbox::Mount {
                    host: c.clone(),
                    guest: format!("{}/claim.bin", layout.inputs),
                },
                arena_sandbox::Mount {
                    host: p.clone(),
                    guest: format!("{}/proof.bin", layout.inputs),
                },
            ],
            collect: vec![],
            out_dir: None,
            wall_timeout: base.wall_timeout,
        })
        .collect();
    let outs = r.run_steps(&base, &steps)?;
    if outs.is_empty() || outs.len() > pairs.len() {
        return Err(ExecError::Infra(format!(
            "run_steps returned {} outcomes for {} steps",
            outs.len(),
            pairs.len()
        )));
    }
    let v: Vec<_> = outs.into_iter().map(|o| (verdict(&o), o)).collect();
    if v.len() < pairs.len() && v.last().is_some_and(|(x, _)| *x == Verdict::Accept) {
        return Err(ExecError::Infra(
            "sandbox stopped a batch after an accepting step".into(),
        ));
    }
    Ok(v)
}

/// Label a case for summaries without leaking held-out ids.
pub fn case_label(id: &str, public: bool) -> String {
    if public {
        format!("case {id:?}")
    } else {
        "a held-out case".to_string()
    }
}
