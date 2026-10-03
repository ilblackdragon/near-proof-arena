//! Helpers shared by the stages that run entry points.

use crate::executor::{describe_exit, entry_spec, failure_reason, ExecError, JobRun, MAX_BUNDLE_BYTES};
use crate::jobs::{BuildOutputs, RunLimits};
use crate::oracle::Case;
use arena_sandbox::{ExitStatus, SandboxOutcome};
use arena_types::candidate::EntrySection as EntryPoints;
use arena_types::{Digest, ObligationId, ReasonCode};
use std::path::{Path, PathBuf};

/// Fetch and safely unpack the build bundle (bound to `build.bundle` by
/// TreeDigest); check the entry points are executable regular files in it.
pub fn fetch_bundle(r: &mut JobRun<'_>, build: &BuildOutputs, entry: &EntryPoints) -> Result<PathBuf, ExecError> {
    let archive = build.bundle_archive.as_ref().ok_or_else(|| ExecError::Infra("build outputs carry no bundle_archive".into()))?;
    let x = r.fetch_tree(archive, &build.bundle, MAX_BUNDLE_BYTES, "bundle")?;
    for (e, want) in [(&entry.prepare, &build.prepare), (&entry.prove, &build.prove)] {
        match x.tree.files.get(e.as_str()) {
            Some(f) if f.mode == arena_archive::FileMode::Exec && &f.digest == want => {}
            _ => return Err(ExecError::Infra(format!("bundle lacks executable {e:?} with the built digest {want}"))),
        }
    }
    // The verifier artifact: the npai-v1 bytecode, else the built `verify`.
    let (vpath, needs_exec) = match (&entry.verify_route, &entry.verifier_bytecode) {
        (Some(arena_types::candidate::VerifyRoute::NpaiV1), Some(bc)) => (bc, false),
        _ => (&entry.verify, true),
    };
    match x.tree.files.get(vpath.as_str()) {
        Some(f) if (!needs_exec || f.mode == arena_archive::FileMode::Exec) && f.digest == build.verify => {}
        _ => return Err(ExecError::Infra(format!("bundle lacks the verifier artifact {vpath:?} with the built digest {}", build.verify))),
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
    if o.pids_limit_hit {
        return Ok(Err(fail(ObligationId::ResourceLimits, ReasonCode::ResourceLimit, format!("prepare hit the process limit ({})", describe_exit(&o)))));
    }
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
    pub verifier: &'p Verifier,
}

/// What `verify` actually executes (selected by `entry.verify_route`).
#[derive(Clone, Debug)]
pub enum Verifier {
    /// `native` route: the candidate's built `verify` (bundle path).
    Candidate,
    /// `npai-v1`: the JUDGE's `npai-verify` on the judge-built bytecode, at
    /// the challenge's `verify_fuel`, bound to the certified digest.
    Npai {
        tool: PathBuf,
        image: PathBuf,
        fuel: u64,
        digest_hex: String,
        /// Lean reference (`arena-interp-ref`) run as a shadow on small inputs.
        shadow: Option<PathBuf>,
    },
    /// `native-lean`: the judge-built native verifier from FORMAL_CHECK.
    NativeLean { binary: PathBuf },
}

/// Shadow inputs above this size (claim + proof + public) are not re-run on
/// the (much slower) Lean reference.
pub const SHADOW_MAX_INPUT_BYTES: u64 = 64 * 1024;
const SHADOW_TIMEOUT_MS: u64 = 30_000;

/// Pick the verifier for this run. `Ok(Err(why))` = this worker cannot
/// serve the route (gates stay UNKNOWN).
pub fn verifier_for(
    r: &mut JobRun<'_>,
    j: &crate::jobs::ExecJob,
    bundle: &Path,
    shadow: bool,
) -> Result<Result<Verifier, String>, ExecError> {
    use arena_types::candidate::VerifyRoute;
    Ok(match j.manifest.entry.verify_route {
        None | Some(VerifyRoute::Native) => Ok(Verifier::Candidate),
        Some(VerifyRoute::NpaiV1) => {
            let Some(tool) = r.ctx.npai_verify.clone() else {
                return Ok(Err("verify_route npai-v1: this worker has no judge npai-verify (ARENA_NPAI_VERIFY)".into()));
            };
            let Some(fp) = &j.challenge.formal_params else {
                return Ok(Err("verify_route npai-v1: the challenge has no formal_params.verify_fuel".into()));
            };
            let bc = j.manifest.entry.verifier_bytecode.clone().unwrap_or_default();
            Ok(Verifier::Npai {
                tool,
                image: bundle.join(bc),
                fuel: fp.verify_fuel,
                digest_hex: j.build.verify.hex().to_string(),
                shadow: if shadow { r.ctx.interp_ref.clone() } else { None },
            })
        }
        Some(VerifyRoute::NativeLean) => {
            let Some(d) = &j.build.native_verifier else {
                return Ok(Err("verify_route native-lean: no judge-built native verifier recorded for this run (FORMAL_CHECK)".into()));
            };
            let b = r.fetch(d, 1 << 30)?;
            let p = r.fresh("native-verify");
            std::fs::write(&p, b)?;
            std::fs::set_permissions(&p, std::os::unix::fs::PermissionsExt::from_mode(0o755))?;
            Ok(Verifier::NativeLean { binary: p })
        }
    })
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
    // Hitting a resource cap is a RESOURCE_LIMITS fact even if the entry
    // point itself exited 0 (e.g. a fork bomb left behind).
    if o.pids_limit_hit {
        return Ok(Err(fail(ResourceLimits, ReasonCode::ResourceLimit, format!("prove hit the process limit ({})", describe_exit(&o)))));
    }
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
    /// `npai-verify --expect-digest` mismatch (exit 3): the bytes executed are
    /// not the certified ones. Never a reject, never an accept:
    /// `ARTIFACT_BINDING_FAILED`.
    BindingMismatch,
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
    let io_args = ["--public", "@in/public", "--claim", "@in/claim.bin", "--proof", "@in/proof.bin"];
    let io_files: [(&Path, &str); 3] = [(public_dir, "public"), (claim, "claim.bin"), (proof, "proof.bin")];
    let mut spec = match env.verifier {
        Verifier::Candidate => entry_spec(&layout, bundle, &entry.verify, &io_args, &io_files, limits.max_verify_ms, limits),
        Verifier::Npai { tool, image, fuel, digest_hex, .. } => {
            let fuel = fuel.to_string();
            let mut args = vec!["--image", "@in/verifier.npai"];
            args.extend(io_args);
            args.extend(["--fuel", fuel.as_str(), "--expect-digest", digest_hex.as_str()]);
            let mut files = io_files.to_vec();
            files.push((image.as_path(), "verifier.npai"));
            judge_spec(&layout, tool, "npai-verify", &args, &files, limits.max_verify_ms, limits)
        }
        Verifier::NativeLean { binary } => judge_spec(&layout, binary, "verify", &io_args, &io_files, limits.max_verify_ms, limits),
    };
    spec.env.push(("ARENA_STAGE".into(), "verify".into()));
    spec.cpu_set = env.cpu_set.clone();
    let o = r.run(&spec)?;
    let v = verdict_for(env.verifier, o.exit);
    if let Verifier::Npai { shadow: Some(reference), image, fuel, .. } = env.verifier {
        shadow_check(r, env, reference, image, *fuel, claim, proof, &o, v)?;
    }
    Ok((v, o))
}

/// CONTRACTS §4 exit codes (+ npai-verify's 3 = digest mismatch).
pub fn verdict_for(verifier: &Verifier, exit: ExitStatus) -> Verdict {
    match (verifier, exit) {
        (_, ExitStatus::Exited(0)) => Verdict::Accept,
        (_, ExitStatus::Exited(1)) => Verdict::Reject,
        (Verifier::Npai { .. }, ExitStatus::Exited(3)) => Verdict::BindingMismatch,
        (_, ExitStatus::TimedOut) => Verdict::TimedOut,
        _ => Verdict::Error,
    }
}

/// Spec running a JUDGE-owned executable (mounted read-only at
/// `<inputs>/judge/<name>`), never anything from the candidate bundle.
fn judge_spec(
    layout: &arena_sandbox::GuestLayout,
    exe: &Path,
    name: &str,
    args: &[&str],
    files: &[(&Path, &str)],
    timeout_ms: u64,
    limits: &RunLimits,
) -> arena_sandbox::SandboxSpec {
    let mut s = entry_spec(layout, Path::new("/nonexistent"), "", args, files, timeout_ms, limits);
    s.ro_mounts.retain(|m| m.guest != format!("{}/bundle", layout.inputs));
    let guest = format!("{}/judge/{name}", layout.inputs);
    s.ro_mounts.push(arena_sandbox::Mount { host: exe.to_path_buf(), guest: guest.clone() });
    s.argv[0] = guest;
    s
}

/// Re-run an npai verification on the Lean reference interpreter and
/// compare (outcome and fuel used). Any disagreement fails the job as an
/// infra error with an ALERT: the trusted Rust interpreter and the Lean
/// semantics it transcribes disagree.
#[allow(clippy::too_many_arguments)]
fn shadow_check(
    r: &mut JobRun<'_>,
    env: &EntryEnv<'_>,
    reference: &Path,
    image: &Path,
    fuel: u64,
    claim: &Path,
    proof: &Path,
    rust: &SandboxOutcome,
    verdict: Verdict,
) -> Result<(), ExecError> {
    if !matches!(verdict, Verdict::Accept | Verdict::Reject) {
        return Ok(());
    }
    let pub_bin = env.public_dir.join("public.bin");
    let size = |p: &Path| std::fs::metadata(p).map(|m| m.len()).unwrap_or(u64::MAX);
    let total = size(&pub_bin).saturating_add(size(claim)).saturating_add(size(proof));
    if total > SHADOW_MAX_INPUT_BYTES {
        r.shadow.1 += 1;
        return Ok(());
    }
    let layout = r.ctx.sandbox.layout();
    let fuel_s = fuel.to_string();
    let args = ["run", "--code", "@in/verifier.npai", "--public", "@in/public.bin", "--claim", "@in/claim.bin", "--proof", "@in/proof.bin", "--fuel", fuel_s.as_str()];
    let files: [(&Path, &str); 4] = [(image, "verifier.npai"), (&pub_bin, "public.bin"), (claim, "claim.bin"), (proof, "proof.bin")];
    let mut limits = env.limits.clone();
    limits.max_ram_bytes = limits.max_ram_bytes.max(1 << 30);
    let spec = judge_spec(&layout, reference, "arena-interp-ref", &args, &files, SHADOW_TIMEOUT_MS, &limits);
    let o = r.run(&spec)?;
    let lean_verdict = match o.exit {
        ExitStatus::Exited(0) => Verdict::Accept,
        ExitStatus::Exited(1) | ExitStatus::Exited(2) => Verdict::Reject,
        _ => {
            // Too slow / resource-bound on the reference: no comparison.
            r.shadow.1 += 1;
            return Ok(());
        }
    };
    let field = |out: &[u8], k: &str| -> Option<String> {
        let v: serde_json::Value = serde_json::from_slice(out.split(|b| *b == b'\n').next()?).ok()?;
        Some(v.get(k)?.to_string())
    };
    let (ro, lo) = (field(&rust.stdout_trunc, "outcome"), field(&o.stdout_trunc, "outcome"));
    let (rf, lf) = (field(&rust.stdout_trunc, "fuel_used"), field(&o.stdout_trunc, "fuel_used"));
    let outcome_differs = ro.is_some() && lo.is_some() && ro != lo;
    let fuel_differs = rf.is_some() && lf.is_some() && rf != lf;
    if lean_verdict != verdict || outcome_differs || fuel_differs {
        return Err(ExecError::Infra(format!(
            "ALERT: npai interpreter disagreement (Rust npai-verify {verdict:?} {ro:?}/{rf:?} vs Lean arena-interp-ref {lean_verdict:?} {lo:?}/{lf:?}) on image {}",
            Digest::of_bytes(&std::fs::read(image).unwrap_or_default())
        )));
    }
    r.shadow.0 += 1;
    Ok(())
}

/// Label a case for summaries without leaking held-out ids.
pub fn case_label(id: &str, public: bool) -> String {
    if public {
        format!("case {id:?}")
    } else {
        "a held-out case".to_string()
    }
}
