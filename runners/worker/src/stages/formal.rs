//! `FORMAL_CHECK`: the formal gates (`FORMAL_*`, `AXIOM_AUDIT`) via
//! `runners/formal-checker`, which runs every step touching candidate
//! content through this worker's shared sandbox (`SandboxRunner`).
//!
//! The judge-side inputs (trusted Lean packages, expected-statement
//! template) come from the worker's formal configuration, keyed by the
//! challenge's `formal_spec.relation_decl`. Without them every required
//! formal gate is `UNKNOWN` (never PASS). `ARTIFACT_BINDING` (built artifact
//! digests ↔ certified artifact descriptions) is not implemented by the
//! checker yet and is reported `UNKNOWN` when required.

use crate::executor::{ExecError, JobRun, StageOut, MAX_PACKAGE_BYTES};
use crate::gate::Gate;
use crate::jobs::FormalCheckJob;
use arena_formal_checker::{CheckRequest, FormalChecker, Limits, Policy, SandboxRunner, TemplateExpected};
use arena_types::{GateResult, GateStatus, ObligationId, ReasonCode};

/// Map challenge rechecker ids onto the checker's ids.
fn rechecker_id(s: &str) -> Option<&'static str> {
    match s {
        "lean4checker" | "leanchecker" => Some("leanchecker"),
        "nanoda" | "nanoda_bin" => Some("nanoda"),
        "lean4lean" => Some("lean4lean"),
        _ => None,
    }
}

pub fn run(r: &mut JobRun<'_>, j: &FormalCheckJob) -> Result<StageOut, ExecError> {
    let chal = &j.challenge;
    let owned = crate::jobs::JobKind::FormalCheck.owned_gates();
    let required: Vec<ObligationId> = owned.iter().copied().filter(|g| chal.required_obligations.contains(g)).collect();
    let mut out = StageOut { used_sandbox: true, ..Default::default() };
    let unknown_all = |out: &mut StageOut, why: &str| {
        for g in &required {
            let mut gate = Gate::start(*g);
            gate.note(why.to_string());
            out.gates.push(gate.finish(GateStatus::Unknown, true));
        }
    };
    let relation = &chal.semantic_scope.formal_spec.relation_decl;
    let Some(cfg) = r.ctx.formal.as_ref().and_then(|f| f.challenges.get(relation)).cloned() else {
        unknown_all(&mut out, &format!("formal checker not configured on this worker for relation {relation}"));
        return Ok(out);
    };
    let Some(formal) = &j.manifest.formal else {
        for g in &required {
            let mut gate = Gate::start(*g);
            gate.fail(ReasonCode::CertificateMissing, "candidate.toml has no [formal] section");
            out.gates.push(gate.finish(GateStatus::Unknown, true));
        }
        return Ok(out);
    };
    let expected: TemplateExpected = serde_json::from_value(cfg.expected.clone()).map_err(|e| ExecError::Infra(format!("formal config expected: {e}")))?;
    let mut recheckers = vec![];
    for id in &chal.toolchain_policy.recheckers {
        match rechecker_id(id) {
            Some(x) => recheckers.push(x.to_string()),
            None => {
                unknown_all(&mut out, &format!("challenge requires rechecker {id:?}, which this worker does not provide"));
                return Ok(out);
            }
        }
    }
    let tools = match arena_formal_checker::toolchain::ToolPaths::discover() {
        Ok(t) => t,
        Err(e) => return Err(ExecError::Infra(format!("formal toolchain: {e}"))),
    };

    // The candidate's formal tree, bound to the build's formal_tree digest.
    let bytes = r.fetch(&j.ctx.package_digest, MAX_PACKAGE_BYTES)?;
    let pkg = r.fresh("pkg");
    let x = arena_archive::ingest_bytes(&bytes, &pkg, &arena_archive::Limits::default()).map_err(|e| ExecError::Infra(format!("package: {e}")))?;
    let formal_dir = x.root.join(&formal.lean_project);
    let ft = arena_archive::tree_from_dir(&formal_dir, &arena_archive::Limits::default())?.digest();
    if ft != j.build.formal_tree || ft != j.verified_surface.formal_tree {
        return Err(ExecError::Infra(format!("formal tree {ft} does not match the run's verified surface")));
    }
    if formal.certificate != j.verified_surface.certificate_decl {
        return Err(ExecError::Infra("certificate name does not match the run's verified surface".into()));
    }

    let runner = match SandboxRunner::new(r.ctx.sandbox.clone(), r.fresh("fc-sandbox")) {
        Ok(x) => x,
        Err(e) => {
            unknown_all(&mut out, &format!("formal checker cannot run on this sandbox: {e}"));
            return Ok(out);
        }
    };
    let checker = FormalChecker::new(tools, Box::new(runner));
    let mut policy = Policy { axiom_allowlist: chal.toolchain_policy.axiom_allowlist.clone(), required_recheckers: recheckers, ..Policy::default() };
    policy.gates.retain(|g| chal.required_obligations.contains(&g.gate) || g.gate == ObligationId::AxiomAudit);
    policy.conjunct_gates = cfg.conjunct_gates.clone();
    let cache_dir = r.ctx.work_root.join("formal-ref-cache");
    let work_dir = r.fresh("formal-work");
    let req = CheckRequest {
        formal_dir,
        certificate: formal.certificate.clone(),
        trusted: cfg.trusted.clone(),
        expected: &expected,
        challenge_digest: Some(j.ctx.challenge_digest.clone()),
        policy,
        limits: Limits::default(),
        work_dir,
        cache_dir,
    };
    r.check_cancel()?;
    let report = checker.check(&req);
    let report_json = serde_json::to_vec(&report).map_err(|e| ExecError::Infra(e.to_string()))?;
    let rd = r.upload("formal check report", &report_json, true)?;
    out.log.extend(report.warnings.iter().take(20).cloned());
    let mut gates: Vec<GateResult> = report.gates.into_iter().filter(|g| owned.contains(&g.gate)).collect();
    for g in &mut gates {
        g.evidence.push(arena_types::EvidenceRef { label: "formal check report".into(), digest: rd.clone(), public: true });
        g.evidence.truncate(64);
    }
    for g in &required {
        if gates.iter().any(|x| x.gate == *g) {
            continue;
        }
        let mut gate = Gate::start(*g);
        if *g == ObligationId::FormalZk && chal.not_applicable_gates.contains(g) {
            gate.note("not applicable to this challenge's privacy profile");
            out.gates.push(gate.finish(GateStatus::NotApplicable, true));
        } else {
            gate.note(format!("{g:?} is not checked by this worker's formal checker yet"));
            out.gates.push(gate.finish(GateStatus::Unknown, true));
        }
    }
    out.gates.extend(gates);
    out.evidence_graph = Some(report.evidence_graph);
    Ok(out)
}
