//! `FORMAL_CHECK`: the formal gates (`FORMAL_*`, `AXIOM_AUDIT`) and
//! `ARTIFACT_BINDING`, via `runners/formal-checker`, which runs every step
//! touching candidate content through this worker's shared sandbox
//! (`SandboxRunner`): bwrap-dev with the host-installed tools, or firecracker
//! with the digest-pinned lean-checker image as the root of every run.
//!
//! Judge inputs:
//! * per-challenge config `runners/formal-checker/challenges/<name>.json`
//!   (`arena-formal-challenge-v1`: trusted Lean packages, reserved prefixes,
//!   Expected template), resolved against a clean checkout
//!   (`ARENA_FORMAL_REPO`);
//! * the Expected statement data: the challenge's `security_profile` and
//!   `formal_params`, and the judge-computed artifact digests —
//!   `sha256(public_dir/public.bin)` from the judge-run `prepare` and the
//!   sha256 of the verifier artifact (`verifier_bytecode` for `npai-v1`,
//!   the built `verify` otherwise). A certificate for different artifacts
//!   therefore has the wrong type.
//!
//! `ARTIFACT_BINDING` is decided from that construction: it passes only when
//! the certificate's type is exactly the statement about the built artifacts
//! and every kernel recheck accepts; a type mismatch fails it with
//! `ARTIFACT_BINDING_FAILED`. Without a config for the challenge, or with a
//! checker whose identity differs from `toolchain_policy.checker_image`,
//! every required formal gate is `UNKNOWN` (never PASS).

use crate::executor::{ExecError, JobRun, StageOut, MAX_PACKAGE_BYTES};
use crate::gate::Gate;
use crate::jobs::{FormalCheckJob, RunLimits};
use arena_formal_checker::native::{NativeLeanRoute, VerifierRoute};
use arena_formal_checker::{
    toolchain::ToolPaths, ChallengeFormalConfig, CheckRequest, ExpectedInputs, FormalChecker, Limits, Policy, SandboxRunner,
};
use arena_types::candidate::VerifyRoute;
use arena_types::{Digest, GateResult, GateStatus, ObligationId, ReasonCode};
use std::path::PathBuf;

/// Where the worker finds its formal-checking inputs.
#[derive(Clone, Debug, Default)]
pub struct FormalEnv {
    /// Clean checkout (git-tracked files only) holding the trusted packages
    /// and templates the challenge configs point at.
    pub repo: PathBuf,
    /// `arena-formal-challenge-v1` configs (default `<repo>/runners/formal-checker/challenges`).
    pub configs_dir: PathBuf,
    /// Installed lean-checker images (`<hex>/` + `<hex>.json`), required on
    /// production (non-demo) sandboxes.
    pub images_dir: Option<PathBuf>,
}

/// Map challenge rechecker ids onto the checker's ids.
fn rechecker_id(s: &str) -> Option<&'static str> {
    match s {
        "lean4checker" | "leanchecker" => Some("leanchecker"),
        "nanoda" | "nanoda_bin" => Some("nanoda"),
        "lean4lean" => Some("lean4lean"),
        _ => None,
    }
}

fn find_config(env: &FormalEnv, name: &str) -> Result<Option<ChallengeFormalConfig>, ExecError> {
    let Ok(rd) = std::fs::read_dir(&env.configs_dir) else { return Ok(None) };
    for e in rd.flatten() {
        let p = e.path();
        if p.extension().is_some_and(|x| x == "json") {
            let c = ChallengeFormalConfig::load(&p).map_err(|e| ExecError::Infra(format!("{}: {e}", p.display())))?;
            if c.challenge == name {
                return Ok(Some(c));
            }
        }
    }
    Ok(None)
}

/// Tools + run root for this sandbox. Production backends run the tools
/// from a lean-checker image whose tool identity matches the challenge.
fn tools_for(r: &JobRun<'_>, env: &FormalEnv) -> Result<(ToolPaths, arena_sandbox::Rootfs, String), String> {
    if r.ctx.sandbox.tier_cap().is_some() {
        let t = ToolPaths::discover().map_err(|e| format!("formal toolchain: {e}"))?;
        return Ok((t, arena_sandbox::Rootfs::BackendDefault, "host-installed tools (DEMO)".into()));
    }
    let images = env.images_dir.as_ref().ok_or("no lean-checker images dir configured (ARENA_LEAN_CHECKER_IMAGES)")?;
    // The newest installed image (by manifest mtime).
    let mut metas: Vec<(std::time::SystemTime, PathBuf)> = std::fs::read_dir(images)
        .map_err(|e| format!("{}: {e}", images.display()))?
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .filter_map(|p| Some((p.metadata().ok()?.modified().ok()?, p)))
        .collect();
    metas.sort();
    let meta_path = metas.pop().ok_or("no lean-checker image installed")?.1;
    let meta: serde_json::Value = serde_json::from_slice(&std::fs::read(&meta_path).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
    let digest: Digest = meta["digest"].as_str().unwrap_or("").to_string().try_into().map_err(|e: String| e)?;
    let dir = images.join(digest.hex());
    let tools = ToolPaths {
        lean_sysroot: dir.join("arena/tc"),
        lean4export: dir.join("arena/tools/lean4export"),
        nanoda: Some(dir.join("arena/tools/nanoda_bin")).filter(|p| p.is_file()),
        lean4lean: Some(dir.join("arena/tools/lean4lean")).filter(|p| p.is_file()),
        arena_audit: dir.join("arena/tools/arena-audit"),
    };
    Ok((tools, arena_sandbox::Rootfs::Image { path: dir, digest: digest.clone() }, format!("lean-checker image {digest}")))
}

pub fn run(r: &mut JobRun<'_>, j: &FormalCheckJob) -> Result<StageOut, ExecError> {
    let chal = &j.challenge;
    let owned = crate::jobs::JobKind::FormalCheck.owned_gates();
    let required: Vec<ObligationId> = owned.iter().copied().filter(|g| chal.required_obligations.contains(g)).collect();
    let mut out = StageOut { used_sandbox: true, ..Default::default() };
    let all_gates = |out: &mut StageOut, status: GateStatus, reason: Option<ReasonCode>, why: &str| {
        for g in &required {
            let mut gate = Gate::start(*g);
            match reason {
                Some(rc) => gate.fail(rc, why.to_string()),
                None => gate.note(why.to_string()),
            }
            out.gates.push(gate.finish(status, true));
        }
    };
    let Some(env) = r.ctx.formal.clone() else {
        all_gates(&mut out, GateStatus::Unknown, None, "formal checker not configured on this worker");
        return Ok(out);
    };
    let Some(cfg) = find_config(&env, &chal.name)? else {
        all_gates(&mut out, GateStatus::Unknown, None, &format!("no formal configuration for challenge {:?}", chal.name));
        return Ok(out);
    };
    let Some(formal) = &j.manifest.formal else {
        all_gates(&mut out, GateStatus::Unknown, Some(ReasonCode::CertificateMissing), "candidate.toml has no [formal] section");
        return Ok(out);
    };
    let mut recheckers = vec![];
    for id in &chal.toolchain_policy.recheckers {
        match rechecker_id(id) {
            Some(x) => recheckers.push(x.to_string()),
            None => {
                all_gates(&mut out, GateStatus::Unknown, None, &format!("challenge requires rechecker {id:?}, which this worker does not provide"));
                return Ok(out);
            }
        }
    }
    let (tools, rootfs, tools_label) = match tools_for(r, &env) {
        Ok(x) => x,
        Err(e) => return Err(ExecError::Infra(e)),
    };
    let checker_id = tools.image_digest().map_err(|e| ExecError::Infra(format!("checker identity: {e}")))?;
    let pinned = &chal.toolchain_policy.checker_image;
    let placeholder = pinned.hex().bytes().all(|b| b == b'0');
    if &checker_id != pinned && !placeholder {
        if chal.tier == arena_types::challenge::Tier::Demo {
            out.log.push(format!("checker identity {checker_id} differs from the challenge's {pinned} (demo only)"));
        } else {
            all_gates(
                &mut out,
                GateStatus::Unknown,
                None,
                &format!("this worker's checker ({tools_label}, identity {checker_id}) is not the challenge's pinned checker {pinned}"),
            );
            return Ok(out);
        }
    }

    // The candidate's formal tree, bound to the verified surface.
    let bytes = r.fetch(&j.ctx.package_digest, MAX_PACKAGE_BYTES)?;
    let pkg = r.fresh("pkg");
    let x = arena_archive::ingest_bytes(&bytes, &pkg, &arena_archive::Limits::default()).map_err(|e| ExecError::Infra(format!("package: {e}")))?;
    let formal_dir = x.root.join(&formal.lean_project);
    let ft = arena_archive::tree_from_dir(&formal_dir, &arena_archive::Limits::default())?.digest();
    if ft != j.build.formal_tree || ft != j.verified_surface.formal_tree || formal.certificate != j.verified_surface.certificate_decl {
        return Err(ExecError::Infra(format!("formal tree {ft} / certificate do not match the run's verified surface")));
    }

    // Judge-computed artifact digests for the statement.
    let limits = RunLimits::from_challenge(chal);
    let public_dir = super::common::fetch_public(r, &j.build, &limits)?;
    let public_bin = public_dir.join("public.bin");
    let npai = j.manifest.entry.verify_route == Some(VerifyRoute::NpaiV1);
    let mut binding = Gate::start(ObligationId::ArtifactBinding);
    let public_digest_hex = match std::fs::read(&public_bin) {
        Ok(b) => Digest::of_bytes(&b).hex().to_string(),
        Err(_) => {
            binding.fail(ReasonCode::ArtifactBindingFailed, "judge-run prepare produced no public_dir/public.bin, which the statement pins");
            let mut gates = vec![binding.finish(GateStatus::Unknown, true)];
            for g in required.iter().filter(|g| **g != ObligationId::ArtifactBinding) {
                let mut gate = Gate::start(*g);
                gate.note("not checked: no public.bin to bind the statement to");
                gates.push(gate.finish(GateStatus::Unknown, true));
            }
            gates.retain(|g| required.contains(&g.gate));
            out.gates = gates;
            return Ok(out);
        }
    };
    // BuildOutputs.verify is the verifier artifact of the verified surface:
    // the npai-v1 bytecode digest, else the built `verify`.
    let verifier_digest_hex = j.build.verify.hex().to_string();
    let route = match j.manifest.entry.verify_route {
        Some(VerifyRoute::NpaiV1) => VerifierRoute::Standard,
        Some(VerifyRoute::NativeLean) => match (&formal.verifier_model, &formal.verifier_model_module) {
            (Some(d), Some(m)) => VerifierRoute::NativeLean(NativeLeanRoute::new(d, m)),
            _ => VerifierRoute::CandidateNative,
        },
        // A candidate-built native verifier has no judge build: never admitted
        // on a formal statement (the checker fails ARTIFACT_BINDING).
        None | Some(VerifyRoute::Native) => VerifierRoute::CandidateNative,
    };
    let inputs = match ExpectedInputs::from_definition(chal, public_digest_hex.clone(), verifier_digest_hex.clone()) {
        Ok(i) => i,
        Err(e) => return Err(ExecError::Infra(format!("expected statement inputs: {e}"))),
    };
    let expected = match &route {
        VerifierRoute::NativeLean(_) => cfg.expected_native_lean(&env.repo, &inputs),
        _ => cfg.expected(&env.repo, &inputs),
    }
    .map_err(|e| ExecError::Infra(format!("expected statement: {e}")))?;

    let runner = match SandboxRunner::new(r.ctx.sandbox.clone(), r.fresh("fc-sandbox")) {
        Ok(x) => x.with_rootfs(rootfs),
        Err(e) => {
            all_gates(&mut out, GateStatus::Unknown, None, &format!("formal checker cannot run on this sandbox: {e}"));
            return Ok(out);
        }
    };
    let checker = FormalChecker::new(tools, Box::new(runner));
    let mut policy = Policy {
        axiom_allowlist: chal.toolchain_policy.axiom_allowlist.clone(),
        required_recheckers: recheckers,
        reserved_prefixes: cfg.reserved_prefixes.clone(),
        ..Policy::default()
    };
    policy.gates.retain(|g| chal.required_obligations.contains(&g.gate) || g.gate == ObligationId::AxiomAudit);
    let req = CheckRequest {
        formal_dir,
        certificate: formal.certificate.clone(),
        trusted: cfg.trusted_packages(&env.repo),
        expected: &expected,
        challenge_digest: Some(j.ctx.challenge_digest.clone()),
        policy,
        limits: Limits::default(),
        work_dir: r.fresh("formal-work"),
        cache_dir: r.ctx.work_root.join("formal-ref-cache"),
        route,
    };
    r.check_cancel()?;
    let report = checker.check(&req);
    let report_json = serde_json::to_vec(&report).map_err(|e| ExecError::Infra(e.to_string()))?;
    let rd = r.upload("formal check report", &report_json, true)?;
    out.log.push(format!("checker: {tools_label}; identity {checker_id}"));
    // native-lean: ship the judge-built verifier to the later stages.
    if let Some(nv) = &report.native_verifier {
        let b = std::fs::read(&nv.path).map_err(|e| ExecError::Infra(format!("native verifier: {e}")))?;
        if Digest::of_bytes(&b) != nv.digest {
            return Err(ExecError::Infra("native verifier changed after the judge build".into()));
        }
        let d = r.upload("judge-built native verifier", &b, true)?;
        out.native_verifier = Some(d);
    }
    out.log.extend(report.warnings.iter().take(20).cloned());
    let mut gates: Vec<GateResult> = report.gates.into_iter().filter(|g| owned.contains(&g.gate)).collect();
    for g in &mut gates {
        g.evidence.push(arena_types::EvidenceRef { label: "formal check report".into(), digest: rd.clone(), public: true });
        g.evidence.truncate(64);
    }

    // ARTIFACT_BINDING from the statement construction.
    binding.note(format!(
        "statement pins sha256(public.bin) = {public_digest_hex} and verifier ({}) = {verifier_digest_hex}",
        if npai { "npai-v1 bytecode" } else { "native verify" }
    ));
    let mismatch = gates.iter().any(|g| g.reason_codes.contains(&ReasonCode::TheoremTypeMismatch));
    let all_pass = !gates.is_empty() && gates.iter().all(|g| g.status == GateStatus::Pass);
    let binding_status = if mismatch {
        binding.fail(ReasonCode::ArtifactBindingFailed, "certificate does not prove the statement about the built artifacts (wrong or stale binding)");
        GateStatus::Unknown
    } else if all_pass {
        GateStatus::Pass
    } else {
        binding.note("undetermined: the certificate did not check");
        GateStatus::Unknown
    };
    // Routes other than Standard get their ARTIFACT_BINDING from the checker
    // (judge native build / no judge build); merge our statement verdict in.
    if let Some(cb) = gates.iter_mut().find(|g| g.gate == ObligationId::ArtifactBinding) {
        if mismatch && cb.status != GateStatus::Fail {
            cb.status = GateStatus::Fail;
            cb.reason_codes.push(ReasonCode::ArtifactBindingFailed);
        }
    } else if required.contains(&ObligationId::ArtifactBinding) {
        out.gates.push(binding.finish(binding_status, true));
    }
    for g in &required {
        if gates.iter().any(|x| x.gate == *g) || *g == ObligationId::ArtifactBinding {
            continue;
        }
        let mut gate = Gate::start(*g);
        if *g == ObligationId::FormalZk && chal.not_applicable_gates.contains(g) {
            gate.note("not applicable to this challenge's privacy profile");
            out.gates.push(gate.finish(GateStatus::NotApplicable, true));
        } else {
            gate.note(format!("{g:?} is not decided by this worker's formal checker"));
            out.gates.push(gate.finish(GateStatus::Unknown, true));
        }
    }
    out.gates.extend(gates);
    out.evidence_graph = Some(report.evidence_graph);
    Ok(out)
}
