//! Stage C decisions: turn the Lean-side audit (`arena-audit`, Environment
//! API on the rechecked `.olean`s) and the independent NDJSON audit (on the
//! export that the external kernel checked) into findings.

use crate::digest::json_digest;
use crate::findings::{Finding, Scope};
use crate::ndjson::{hex, DeclKind, Export, H};
use arena_types::{Digest, ReasonCode};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeSet, HashMap};

pub const SORRY_AXIOMS: &[&str] = &["sorryAx"];
pub const NATIVE_AXIOMS: &[&str] = &[
    "Lean.ofReduceBool",
    "Lean.ofReduceNat",
    "Lean.trustCompiler",
];

/// Classify one axiom in the certificate's closure.
pub fn classify_axiom(
    name: &str,
    allowlist: &[String],
    trusted_axioms: &BTreeSet<String>,
) -> Option<ReasonCode> {
    if allowlist.iter().any(|a| a == name) {
        None
    } else if SORRY_AXIOMS.contains(&name) {
        Some(ReasonCode::SorryFound)
    } else if NATIVE_AXIOMS.contains(&name) || name.split('.').any(|c| c == "_native") {
        // `native_decide` (Lean >= 4.2x) emits per-use auxiliary axioms
        // `<decl>._native.native_decide.ax_*` instead of `Lean.ofReduceBool`.
        Some(ReasonCode::NativeEvalFound)
    } else if trusted_axioms.contains(name) {
        // Declared by a judge-pinned module (e.g. a named assumption) but not
        // approved for this challenge/profile.
        Some(ReasonCode::UnapprovedAssumption)
    } else {
        Some(ReasonCode::ForbiddenAxiom)
    }
}

// ---------------------------------------------------------------- Lean side

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", default)]
pub struct LeanClosureEntry {
    pub name: String,
    pub kind: String,
    pub module: String,
    pub origin: String,
    #[serde(rename = "unsafe")]
    pub is_unsafe: bool,
    #[serde(rename = "partial")]
    pub is_partial: bool,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", default)]
pub struct LeanFlagged {
    pub name: String,
    pub module: String,
    pub implemented_by: Option<String>,
    #[serde(rename = "extern")]
    pub is_extern: bool,
    pub init: bool,
    #[serde(rename = "unsafe")]
    pub is_unsafe: bool,
    #[serde(rename = "partial")]
    pub is_partial: bool,
    pub opaque: bool,
    /// `@[export <sym>]`: exposes/overrides a C symbol in compiled code.
    pub export: Option<String>,
}

/// A non-trusted `@[csimp]` (compiler substitution) entry `from ↦ to` proved by `thm`.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", default)]
pub struct LeanCSimp {
    pub thm: String,
    /// Lean's escaped rendering of `thm` (for lean4export's name decoder).
    pub thm_escaped: String,
    pub from: String,
    pub to: String,
    pub origin: String,
    pub from_origin: String,
    /// The theorem's statement is literally `@from = @to` (Lean's requirement).
    pub statement_ok: bool,
    pub axioms: Vec<String>,
    pub unsafe_or_partial: Vec<String>,
    pub closure_missing: Vec<String>,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", default)]
pub struct LeanAxiomUser {
    pub decl: String,
    pub axiom: String,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", default)]
pub struct LeanAudit {
    pub import_ok: bool,
    pub import_error: Option<String>,
    pub fatal: Option<String>,
    pub certificate_found: Option<bool>,
    pub certificate_kind: Option<String>,
    pub certificate_module: Option<String>,
    pub certificate_origin: Option<String>,
    pub level_params_ok: Option<bool>,
    pub type_equal: Option<bool>,
    pub type_via_expected_const: Option<bool>,
    pub certificate_type_preview: Option<String>,
    pub expected_preview: Option<String>,
    pub axioms: Vec<String>,
    pub closure: Vec<LeanClosureEntry>,
    pub closure_missing: Vec<String>,
    pub untrusted_in_statement: Vec<String>,
    pub flagged: Vec<LeanFlagged>,
    // native-lean route
    pub model_found: Option<bool>,
    pub model_kind: Option<String>,
    pub model_module: Option<String>,
    pub model_origin: Option<String>,
    pub model_axioms: Vec<String>,
    pub model_closure: Vec<LeanClosureEntry>,
    /// Non-trusted compiler-substitution lemmas (audited even though they are
    /// outside the certificate closure: they change compiled code).
    pub csimp: Vec<LeanCSimp>,
    /// Axioms reachable from ANY constant of ANY candidate module.
    pub candidate_axioms: Vec<String>,
    pub candidate_axiom_users: Vec<LeanAxiomUser>,
    pub candidate_const_count: Option<u64>,
}

/// Findings for compiler-affecting declarations and the candidate-wide
/// axiom audit (both outside the certificate's dependency closure).
pub fn lean_compiled_code_findings(a: &LeanAudit, allowlist: &[String], trusted_axioms: &BTreeSet<String>) -> Vec<Finding> {
    let mut f = Vec::new();
    if !a.import_ok || a.fatal.is_some() {
        return f;
    }
    for c in &a.csimp {
        if !c.statement_ok {
            f.push(Finding::new(
                ReasonCode::RecheckFailed,
                Scope::Compiled,
                format!("@[csimp] entry {} ↦ {} via {} is not backed by a theorem `@{} = @{}` (environment inconsistency)", c.from, c.to, c.thm, c.from, c.to),
            ));
        }
        if !c.closure_missing.is_empty() {
            f.push(Finding::new(ReasonCode::RecheckFailed, Scope::Compiled, format!("@[csimp] {} has missing dependencies {:?}", c.thm, c.closure_missing)));
        }
        for ax in &c.axioms {
            if let Some(code) = classify_axiom(ax, allowlist, trusted_axioms) {
                f.push(Finding::new(
                    code,
                    Scope::Compiled,
                    format!("@[csimp] lemma {} (compiled code: {} ↦ {}) depends on axiom {ax}", c.thm, c.from, c.to),
                ));
            }
        }
        for n in &c.unsafe_or_partial {
            f.push(Finding::new(
                ReasonCode::UnapprovedAssumption,
                Scope::Compiled,
                format!("@[csimp] lemma {} depends on candidate unsafe/partial/opaque `{n}`", c.thm),
            ));
        }
    }
    let mut attributed = BTreeSet::new();
    for u in &a.candidate_axiom_users {
        if let Some(code) = classify_axiom(&u.axiom, allowlist, trusted_axioms) {
            attributed.insert(u.axiom.clone());
            f.push(Finding::new(
                code,
                Scope::AxiomAudit,
                format!("candidate declaration {} depends on axiom {} (every candidate declaration is audited)", u.decl, u.axiom),
            ));
        }
    }
    for ax in &a.candidate_axioms {
        if attributed.contains(ax) {
            continue;
        }
        if let Some(code) = classify_axiom(ax, allowlist, trusted_axioms) {
            f.push(Finding::new(code, Scope::AxiomAudit, format!("candidate modules depend on axiom {ax}")));
        }
    }
    f
}

/// Findings about the candidate verifier model spliced into the statement
/// (native-lean route). The model is untrusted code inside a judge statement,
/// so its whole dependency closure is held to the certificate's standard.
pub fn lean_model_findings(
    a: &LeanAudit,
    model_decl: &str,
    model_module: &str,
    allowlist: &[String],
    trusted_axioms: &BTreeSet<String>,
) -> Vec<Finding> {
    let mut f = Vec::new();
    if !a.import_ok || a.fatal.is_some() {
        return f;
    }
    if a.model_found != Some(true) {
        f.push(Finding::new(
            ReasonCode::ArtifactBindingFailed,
            Scope::All,
            format!("verifier model {model_decl} not found"),
        ));
        return f;
    }
    if a.model_origin.as_deref() != Some("candidate")
        || a.model_module.as_deref() != Some(model_module)
    {
        f.push(Finding::new(
            ReasonCode::ArtifactBindingFailed,
            Scope::All,
            format!("verifier model {model_decl} must be declared in candidate module {model_module} (found in {:?}, origin {:?})", a.model_module, a.model_origin),
        ));
    }
    if a.model_kind.as_deref() != Some("def") {
        f.push(Finding::new(
            ReasonCode::UnapprovedAssumption,
            Scope::All,
            format!("verifier model {model_decl} is a {:?}, not a definition (its behaviour would be unknown to the proof)", a.model_kind),
        ));
    }
    for ax in &a.model_axioms {
        if let Some(code) = classify_axiom(ax, allowlist, trusted_axioms) {
            f.push(Finding::new(
                code,
                Scope::All,
                format!("verifier model depends on axiom {ax}"),
            ));
        }
    }
    for c in &a.model_closure {
        if c.origin == "candidate" && (c.is_partial || c.kind == "opaque") {
            f.push(Finding::new(
                ReasonCode::UnapprovedAssumption,
                Scope::All,
                format!(
                    "verifier model uses candidate {} `{}` (opaque/partial)",
                    c.kind, c.name
                ),
            ));
        }
        if c.is_unsafe {
            f.push(Finding::new(
                ReasonCode::NativeEvalFound,
                Scope::All,
                format!("verifier model uses unsafe `{}`", c.name),
            ));
        }
        if c.origin == "trusted" && c.name == model_decl {
            f.push(Finding::new(
                ReasonCode::ShadowedDefinition,
                Scope::All,
                format!("verifier model {model_decl} resolves to a trusted declaration"),
            ));
        }
    }
    f
}

fn is_partial_aux(f: &LeanFlagged) -> bool {
    // `partial def f` compiles to `f` implemented_by `f._unsafe_rec` (unsafe).
    f.name.ends_with("._unsafe_rec")
        || f.implemented_by.as_deref() == Some(&format!("{}._unsafe_rec", f.name))
}

/// `per_conjunct_axioms`: the NDJSON audit attributed axioms per conjunct, so
/// the (whole-certificate) Lean-side axiom findings are left to it; the two
/// axiom sets are still compared by `cross_check`.
pub fn lean_findings(
    a: &LeanAudit,
    allowlist: &[String],
    trusted_axioms: &BTreeSet<String>,
    per_conjunct_axioms: bool,
) -> Vec<Finding> {
    let mut f = Vec::new();
    if !a.import_ok {
        let e = a.import_error.clone().unwrap_or_default();
        let code = if e.contains("already contains") || e.contains("already declared") {
            ReasonCode::ShadowedDefinition
        } else {
            ReasonCode::RecheckFailed
        };
        f.push(Finding::new(
            code,
            Scope::All,
            format!("joint import of expected statement and candidate failed: {e}"),
        ));
        return f;
    }
    if let Some(fatal) = &a.fatal {
        f.push(Finding::unknown(
            ReasonCode::InfraError,
            format!("audit: {fatal}"),
        ));
        return f;
    }
    for fl in &a.flagged {
        if is_partial_aux(fl) && !fl.is_extern && !fl.init {
            continue;
        }
        let mut what = Vec::new();
        if let Some(t) = &fl.implemented_by {
            what.push(format!("@[implemented_by {t}]"));
        }
        if fl.is_extern {
            what.push("@[extern]".into());
        }
        if fl.init {
            what.push("initialize/[init]".into());
        }
        if fl.is_unsafe {
            what.push("unsafe".into());
        }
        if let Some(e) = &fl.export {
            what.push(format!("@[export {e}]"));
        }
        if !what.is_empty() {
            f.push(Finding::new(
                ReasonCode::NativeEvalFound,
                Scope::All,
                format!("candidate declaration {} uses {}", fl.name, what.join(", ")),
            ));
        }
    }
    if !a.untrusted_in_statement.is_empty() {
        f.push(Finding::new(
            ReasonCode::ShadowedDefinition,
            Scope::All,
            format!(
                "expected statement depends on non-trusted declarations: {:?}",
                a.untrusted_in_statement
            ),
        ));
    }
    if a.certificate_found != Some(true) {
        f.push(Finding::new(
            ReasonCode::CertificateMissing,
            Scope::All,
            "certificate constant not found".into(),
        ));
        return f;
    }
    if a.certificate_origin.as_deref() != Some("candidate") {
        f.push(Finding::new(
            ReasonCode::CertificateMissing,
            Scope::All,
            format!(
                "certificate is not declared in a candidate module (origin {:?})",
                a.certificate_origin
            ),
        ));
    }
    if a.type_equal != Some(true) {
        f.push(Finding::new(
            ReasonCode::TheoremTypeMismatch,
            Scope::All,
            format!(
                "certificate type differs from the judge-constructed statement\nexpected: {}\nactual:   {}",
                a.expected_preview.as_deref().unwrap_or("?"),
                a.certificate_type_preview.as_deref().unwrap_or("?")
            ),
        ));
    }
    for ax in a.axioms.iter().filter(|_| !per_conjunct_axioms) {
        if let Some(code) = classify_axiom(ax, allowlist, trusted_axioms) {
            f.push(Finding::new(
                code,
                Scope::Certificate,
                format!("certificate depends on axiom {ax}"),
            ));
        }
    }
    for c in &a.closure {
        if c.origin == "candidate" && (c.is_partial || c.kind == "opaque") {
            f.push(Finding::new(
                ReasonCode::UnapprovedAssumption,
                Scope::Certificate,
                format!("certified path uses candidate {} `{}` (opaque/partial: only its type is known)", c.kind, c.name),
            ));
        }
        if c.is_unsafe {
            f.push(Finding::new(
                ReasonCode::NativeEvalFound,
                Scope::Certificate,
                format!("certified path uses unsafe `{}`", c.name),
            ));
        }
    }
    f
}

// -------------------------------------------------------------- NDJSON side

#[derive(Clone, Debug, Default, Serialize)]
pub struct NdAudit {
    pub certificate_found: bool,
    pub certificate_kind: Option<DeclKind>,
    pub type_equal: bool,
    pub type_via_expected_const: bool,
    pub shadowed: Vec<String>,
    pub missing_trusted: Vec<String>,
    pub axioms: BTreeSet<String>,
    pub unsafe_or_partial: Vec<String>,
    pub closure_count: usize,
    pub closure_digest: Option<Digest>,
    /// (name, kind, decl hash) for every declaration in the certified closure.
    #[serde(skip)]
    pub closure: Vec<(String, DeclKind, String)>,
    pub closure_missing: Vec<String>,
    /// Per-conjunct axiom sets when the proof term is an `And.intro` chain.
    pub conjunct_axioms: Option<Vec<BTreeSet<String>>>,
    pub trusted_axioms: BTreeSet<String>,
    pub model_found: bool,
    pub model_axioms: BTreeSet<String>,
    pub model_closure_digest: Option<Digest>,
}

fn axioms_in(ex: &Export, names: &BTreeSet<String>) -> BTreeSet<String> {
    names
        .iter()
        .filter(|n| ex.decls.get(*n).is_some_and(|d| d.kind == DeclKind::Axiom))
        .cloned()
        .collect()
}

/// native-lean route parameters for the NDJSON audit.
#[derive(Clone, Copy, Debug)]
pub struct NdModel<'a> {
    pub model_decl: &'a str,
    pub inst_decl: &'a str,
}

pub fn nd_audit(
    cand: &Export,
    reference: &Export,
    certificate: &str,
    expected_decl: &str,
    n_conjuncts: usize,
    model: Option<NdModel>,
) -> NdAudit {
    let mut a = NdAudit {
        trusted_axioms: reference
            .decls
            .values()
            .filter(|d| d.kind == DeclKind::Axiom)
            .map(|d| d.name.clone())
            .collect(),
        ..Default::default()
    };
    // (c) every reference declaration present in the candidate env is identical.
    let mut ref_hash: HashMap<&str, H> = HashMap::new();
    for (n, d) in &reference.decls {
        let rh = reference.decl_hash(d);
        ref_hash.insert(n.as_str(), rh);
        if let Some(cd) = cand.decls.get(n) {
            if cand.decl_hash(cd) != rh {
                a.shadowed.push(n.clone());
            }
        }
    }
    a.shadowed.sort();
    let Some(cert) = cand.decls.get(certificate) else {
        return a;
    };
    a.certificate_found = true;
    a.certificate_kind = Some(cert.kind);
    let Some(exp) = reference.decls.get(expected_decl) else {
        return a;
    };
    let Some(exp_val) = exp.value else { return a };
    // (a) syntactic equality after positional renaming of universe params.
    if let Some(m) = model {
        // Statement = (expected lambda) applied to the model constant: accept
        // the beta-reduced form, the literal application, or the judge's
        // instantiation constant whose value is that application.
        let repl = crate::ndjson::const_hash(m.model_decl);
        let inst_hash = reference.lambda_body_instantiated(exp_val, &repl);
        let is_applied = |ex: &Export, e: u32| {
            ex.as_app_of_consts(e) == Some((expected_decl.to_string(), m.model_decl.to_string()))
        };
        let direct = cert.level_params.is_empty()
            && exp.level_params.is_empty()
            && (Some(cand.expr_hash(cert.ty, None)) == inst_hash || is_applied(cand, cert.ty));
        let via_inst = cert.level_params.is_empty()
            && cand
                .const_head(cert.ty)
                .is_some_and(|(n, us)| n == m.inst_decl && us.is_empty())
            && cand.decls.get(m.inst_decl).is_some_and(|d| {
                d.kind == DeclKind::Def
                    && d.level_params.is_empty()
                    && d.value.is_some_and(|v| is_applied(cand, v))
            });
        a.type_equal = direct || via_inst;
        a.type_via_expected_const = via_inst || (direct && is_applied(cand, cert.ty));
        let (mclo, _) = cand.closure([m.model_decl.to_string()]);
        a.model_found = cand.decls.contains_key(m.model_decl);
        a.model_axioms = axioms_in(cand, &mclo);
        a.model_closure_digest = Some(json_digest(
            &mclo
                .iter()
                .map(|n| (n.clone(), hex(&cand.decl_hash(&cand.decls[n]))))
                .collect::<Vec<_>>(),
        ));
    } else if cert.level_params.len() == exp.level_params.len() {
        let subst: HashMap<String, String> = cert
            .level_params
            .iter()
            .cloned()
            .zip(exp.level_params.iter().cloned())
            .collect();
        let ct = cand.expr_hash(cert.ty, Some(&subst));
        a.type_equal = ct == reference.expr_hash(exp_val, None);
        if !a.type_equal {
            if let Some((n, us)) = cand.const_head(cert.ty) {
                let lv_ok = us.len() == exp.level_params.len()
                    && us
                        .iter()
                        .zip(&cert.level_params)
                        .all(|(u, p)| cand.level_is_param(*u, p))
                    && cert
                        .level_params
                        .iter()
                        .zip(&exp.level_params)
                        .all(|(c, e)| c == e);
                if n == expected_decl
                    && lv_ok
                    && cand
                        .decls
                        .get(expected_decl)
                        .is_some_and(|d| ref_hash.get(expected_decl) == Some(&cand.decl_hash(d)))
                {
                    a.type_equal = true;
                    a.type_via_expected_const = true;
                }
            }
        }
    }
    // Statement closure in the reference must be present in the candidate export.
    let mut stmt_consts = BTreeSet::new();
    reference.consts_in(exp_val, &mut Default::default(), &mut stmt_consts);
    stmt_consts.remove(expected_decl);
    let (stmt_closure, _) = reference.closure(stmt_consts);
    if a.type_equal {
        a.missing_trusted = stmt_closure
            .iter()
            .filter(|n| !cand.decls.contains_key(*n))
            .cloned()
            .collect();
    }
    // (b)/(e)/(f) certified closure.
    let (clo, missing) = cand.closure([certificate.to_string()]);
    a.closure_missing = missing.into_iter().collect();
    a.axioms = axioms_in(cand, &clo);
    for n in &clo {
        let d = &cand.decls[n];
        if d.is_unsafe || d.is_partial {
            a.unsafe_or_partial.push(n.clone());
        }
        a.closure.push((n.clone(), d.kind, hex(&cand.decl_hash(d))));
    }
    a.closure_count = a.closure.len();
    a.closure_digest = Some(json_digest(
        &a.closure
            .iter()
            .map(|(n, k, h)| (n, format!("{k:?}"), h))
            .collect::<Vec<_>>(),
    ));
    // Per-conjunct decomposition of the proof term.
    if n_conjuncts > 1 {
        if let Some(v) = cert.value {
            let mut parts = Vec::new();
            let mut cur = v;
            let mut ok = true;
            for _ in 0..n_conjuncts - 1 {
                match cand.as_and_intro(cur) {
                    Some((pa, pb)) => {
                        parts.push(pa);
                        cur = pb;
                    }
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                parts.push(cur);
                let mut per = Vec::new();
                for p in parts {
                    let mut roots = BTreeSet::new();
                    cand.consts_in(p, &mut Default::default(), &mut roots);
                    let (c, _) = cand.closure(roots);
                    per.push(axioms_in(cand, &c));
                }
                a.conjunct_axioms = Some(per);
            }
        }
    }
    a
}

pub fn nd_findings(a: &NdAudit, allowlist: &[String]) -> Vec<Finding> {
    let mut f = Vec::new();
    for ax in &a.model_axioms {
        if let Some(code) = classify_axiom(ax, allowlist, &a.trusted_axioms) {
            f.push(Finding::new(
                code,
                Scope::All,
                format!("verifier model depends on axiom {ax}"),
            ));
        }
    }
    if !a.shadowed.is_empty() {
        f.push(Finding::new(
            ReasonCode::ShadowedDefinition,
            Scope::All,
            format!(
                "candidate environment redefines {} judge-pinned declaration(s): {:?}",
                a.shadowed.len(),
                &a.shadowed[..a.shadowed.len().min(10)]
            ),
        ));
    }
    if !a.certificate_found {
        f.push(Finding::new(
            ReasonCode::CertificateMissing,
            Scope::All,
            "certificate not present in the exported environment".into(),
        ));
        return f;
    }
    if !a.type_equal {
        f.push(Finding::new(
            ReasonCode::TheoremTypeMismatch,
            Scope::All,
            "exported certificate type is not structurally equal to the reference statement".into(),
        ));
    }
    if !a.missing_trusted.is_empty() || !a.closure_missing.is_empty() {
        f.push(Finding::new(
            ReasonCode::RecheckFailed,
            Scope::All,
            format!(
                "export is not closed: missing {:?} {:?}",
                a.missing_trusted, a.closure_missing
            ),
        ));
    }
    match &a.conjunct_axioms {
        Some(per) => {
            for (i, axs) in per.iter().enumerate() {
                for ax in axs {
                    if let Some(code) = classify_axiom(ax, allowlist, &a.trusted_axioms) {
                        f.push(Finding::new(
                            code,
                            Scope::Conjunct(i),
                            format!("conjunct {i} depends on axiom {ax}"),
                        ));
                    }
                }
            }
        }
        None => {
            for ax in &a.axioms {
                if let Some(code) = classify_axiom(ax, allowlist, &a.trusted_axioms) {
                    f.push(Finding::new(
                        code,
                        Scope::Certificate,
                        format!("certificate depends on axiom {ax}"),
                    ));
                }
            }
        }
    }
    for n in &a.unsafe_or_partial {
        f.push(Finding::new(
            ReasonCode::UnapprovedAssumption,
            Scope::Certificate,
            format!("certified path uses unsafe/partial `{n}`"),
        ));
    }
    f
}

/// The two audits are computed from different representations (mapped
/// `.olean` vs kernel-checked NDJSON). They must agree on the decisive facts.
pub fn cross_check(lean: &LeanAudit, nd: &NdAudit) -> Option<Finding> {
    if !lean.import_ok || lean.certificate_found != Some(true) || !nd.certificate_found {
        return None;
    }
    let lean_axioms: BTreeSet<String> = lean.axioms.iter().cloned().collect();
    let mut diffs = Vec::new();
    if lean.type_equal != Some(nd.type_equal) {
        diffs.push(format!(
            "type_equal lean={:?} ndjson={}",
            lean.type_equal, nd.type_equal
        ));
    }
    if lean_axioms != nd.axioms {
        diffs.push(format!(
            "axioms lean={lean_axioms:?} ndjson={:?}",
            nd.axioms
        ));
    }
    (!diffs.is_empty()).then(|| {
        Finding::new(
            ReasonCode::RecheckFailed,
            Scope::All,
            format!("independent audits disagree: {}", diffs.join("; ")),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ndjson::Export;

    const META: &str = r#"{"meta":{"exporter":{"name":"t","version":"0"},"format":{"version":"3.1.0"},"lean":{"githash":"","version":""}}}"#;

    /// Names: 1=P 2=ArenaExpected 3=ArenaExpected.expectedType 4=Candidate 5=Candidate.certificate 6=x 7=y 8=propext 9=cheat
    fn names() -> String {
        [
            r#"{"in":1,"str":{"pre":0,"str":"P"}}"#,
            r#"{"in":2,"str":{"pre":0,"str":"ArenaExpected"}}"#,
            r#"{"in":3,"str":{"pre":2,"str":"expectedType"}}"#,
            r#"{"in":4,"str":{"pre":0,"str":"Candidate"}}"#,
            r#"{"in":5,"str":{"pre":4,"str":"certificate"}}"#,
            r#"{"in":6,"str":{"pre":0,"str":"x"}}"#,
            r#"{"in":7,"str":{"pre":0,"str":"y"}}"#,
            r#"{"in":8,"str":{"pre":0,"str":"propext"}}"#,
            r#"{"in":9,"str":{"pre":0,"str":"cheat"}}"#,
        ]
        .join("\n")
    }

    /// e0 = Prop, e1 = Type, e2 = const P, e3 = fun (x : Prop) => x, e4 = fun (y : Prop) => y (binder renamed)
    fn exprs() -> String {
        [
            r#"{"il":1,"succ":0}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"ie":1,"sort":1}"#,
            r#"{"const":{"name":1,"us":[]},"ie":2}"#,
            r#"{"bvar":0,"ie":3}"#,
            r#"{"ie":4,"lam":{"binderInfo":"default","body":3,"name":6,"type":0}}"#,
            r#"{"ie":5,"lam":{"binderInfo":"implicit","body":3,"name":7,"type":0}}"#,
        ]
        .join("\n")
    }

    fn write(dir: &std::path::Path, name: &str, decls: &[&str]) -> Export {
        let p = dir.join(name);
        let body = format!("{META}\n{}\n{}\n{}\n", names(), exprs(), decls.join("\n"));
        std::fs::write(&p, body).unwrap();
        Export::read(&p, 1 << 30).unwrap()
    }

    fn tmp() -> std::path::PathBuf {
        let d = std::env::temp_dir().join(format!(
            "fc-audit-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&d).unwrap();
        d
    }

    // P : Type := Prop ; expectedType : Type := P (as a "statement" stand-in)
    const DEF_P: &str = r#"{"def":{"all":[1],"hints":"abbrev","levelParams":[],"name":1,"safety":"safe","type":1,"value":0}}"#;
    const DEF_P_ALTERED: &str = r#"{"def":{"all":[1],"hints":"abbrev","levelParams":[],"name":1,"safety":"safe","type":1,"value":1}}"#;
    const DEF_EXP: &str = r#"{"def":{"all":[3],"hints":"abbrev","levelParams":[],"name":3,"safety":"safe","type":1,"value":2}}"#;
    const AX_PROPEXT: &str = r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":8,"type":0}}"#;

    #[test]
    fn statement_equality_and_shadowing() {
        let d = tmp();
        let reference = write(&d, "ref.ndjson", &[DEF_P, DEF_EXP, AX_PROPEXT]);
        // certificate : P (value irrelevant here; kernel checking is nanoda's job)
        let good = write(
            &d,
            "good.ndjson",
            &[
                DEF_P,
                r#"{"thm":{"all":[5],"levelParams":[],"name":5,"type":2,"value":4}}"#,
            ],
        );
        let a = nd_audit(
            &good,
            &reference,
            "Candidate.certificate",
            "ArenaExpected.expectedType",
            1,
            None,
        );
        assert!(
            a.certificate_found
                && a.type_equal
                && a.shadowed.is_empty()
                && a.missing_trusted.is_empty(),
            "{a:?}"
        );
        assert!(nd_findings(&a, &["propext".into()]).is_empty());

        // Same name `P`, different body: statement matches by name but P is shadowed.
        let shadow = write(
            &d,
            "shadow.ndjson",
            &[
                DEF_P_ALTERED,
                r#"{"thm":{"all":[5],"levelParams":[],"name":5,"type":2,"value":4}}"#,
            ],
        );
        let a = nd_audit(
            &shadow,
            &reference,
            "Candidate.certificate",
            "ArenaExpected.expectedType",
            1,
            None,
        );
        assert_eq!(a.shadowed, vec!["P".to_string()]);
        assert!(nd_findings(&a, &[])
            .iter()
            .any(|f| f.code == ReasonCode::ShadowedDefinition));

        // Wrong type (Prop instead of P).
        let wrong = write(
            &d,
            "wrong.ndjson",
            &[
                DEF_P,
                r#"{"thm":{"all":[5],"levelParams":[],"name":5,"type":0,"value":4}}"#,
            ],
        );
        let a = nd_audit(
            &wrong,
            &reference,
            "Candidate.certificate",
            "ArenaExpected.expectedType",
            1,
            None,
        );
        assert!(!a.type_equal);

        // Missing certificate.
        let a = nd_audit(
            &good,
            &reference,
            "Candidate.nope",
            "ArenaExpected.expectedType",
            1,
            None,
        );
        assert!(nd_findings(&a, &[])
            .iter()
            .any(|f| f.code == ReasonCode::CertificateMissing));

        // Axiom in the closure: candidate-declared axiom used by the certificate.
        let ax = write(
            &d,
            "ax.ndjson",
            &[
                DEF_P,
                r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":9,"type":2}}"#,
                r#"{"const":{"name":9,"us":[]},"ie":6}"#,
                r#"{"thm":{"all":[5],"levelParams":[],"name":5,"type":2,"value":6}}"#,
            ],
        );
        let a = nd_audit(
            &ax,
            &reference,
            "Candidate.certificate",
            "ArenaExpected.expectedType",
            1,
            None,
        );
        assert!(a.type_equal);
        assert_eq!(
            a.axioms.iter().cloned().collect::<Vec<_>>(),
            vec!["cheat".to_string()]
        );
        assert!(nd_findings(&a, &["propext".into()])
            .iter()
            .any(|f| f.code == ReasonCode::ForbiddenAxiom));
    }

    #[test]
    fn hashing_ignores_binder_names_and_info() {
        let d = tmp();
        let ex = write(&d, "b.ndjson", &[]);
        assert_eq!(ex.expr_hash(4, None), ex.expr_hash(5, None));
        assert_ne!(ex.expr_hash(0, None), ex.expr_hash(1, None));
    }

    #[test]
    fn malformed_exports_are_rejected() {
        let d = tmp();
        let p = d.join("fwd.ndjson");
        std::fs::write(
            &p,
            format!("{META}\n{{\"in\":1,\"str\":{{\"pre\":5,\"str\":\"x\"}}}}\n"),
        )
        .unwrap();
        assert!(Export::read(&p, 1 << 20).is_err(), "forward name reference");
        std::fs::write(
            &p,
            format!("{META}\n{}\n{}\n{DEF_P}\n{DEF_P}\n", names(), exprs()),
        )
        .unwrap();
        assert!(Export::read(&p, 1 << 20).is_err(), "duplicate declaration");
        std::fs::write(&p, format!("{}\n{}\n", names(), exprs())).unwrap();
        assert!(Export::read(&p, 1 << 20).is_err(), "missing meta");
        std::fs::write(&p, format!("{META}\n{{\"ie\":0,\"natVal\":\"12a\"}}\n")).unwrap();
        assert!(Export::read(&p, 1 << 20).is_err(), "bad nat literal");
        assert!(Export::read(&p, 1).is_err(), "size cap");
    }

    #[test]
    fn axiom_classification() {
        let allow: Vec<String> = vec![
            "propext".into(),
            "Quot.sound".into(),
            "Classical.choice".into(),
        ];
        let trusted: BTreeSet<String> = ["ArenaCore.Assumptions.cr".to_string()].into();
        assert_eq!(classify_axiom("propext", &allow, &trusted), None);
        assert_eq!(
            classify_axiom("sorryAx", &allow, &trusted),
            Some(ReasonCode::SorryFound)
        );
        assert_eq!(
            classify_axiom("Lean.ofReduceBool", &allow, &trusted),
            Some(ReasonCode::NativeEvalFound)
        );
        assert_eq!(
            classify_axiom("C.cert._native.native_decide.ax_1_1", &allow, &trusted),
            Some(ReasonCode::NativeEvalFound)
        );
        assert_eq!(
            classify_axiom("ArenaCore.Assumptions.cr", &allow, &trusted),
            Some(ReasonCode::UnapprovedAssumption)
        );
        assert_eq!(
            classify_axiom("Candidate.cheat", &allow, &trusted),
            Some(ReasonCode::ForbiddenAxiom)
        );
    }
}

/// Independent (NDJSON, nanoda-checked) audit of the `@[csimp]` lemmas the
/// Lean-side audit enumerated: each must be in the export as a theorem whose
/// statement is literally `@from = @to`, and its closure's axioms must be allowed.
pub fn nd_csimp_findings(
    ex: &Export,
    csimp: &[LeanCSimp],
    allowlist: &[String],
    trusted_axioms: &BTreeSet<String>,
) -> Vec<Finding> {
    let mut f = Vec::new();
    for c in csimp {
        let Some(d) = ex.decls.get(&c.thm) else {
            f.push(Finding::new(ReasonCode::RecheckFailed, Scope::Compiled, format!("@[csimp] lemma {} missing from the independent export", c.thm)));
            continue;
        };
        let shape = (d.kind == DeclKind::Thm).then(|| ex.as_eq_of_consts(d.ty, &d.level_params)).flatten();
        match shape {
            Some((from, to, true)) if from == c.from && to == c.to => {}
            other => f.push(Finding::new(
                ReasonCode::RecheckFailed,
                Scope::Compiled,
                format!("@[csimp] lemma {} is not a theorem `@{} = @{}` in the independent export (got {other:?})", c.thm, c.from, c.to),
            )),
        }
        let (clo, missing) = ex.closure([c.thm.clone()]);
        if !missing.is_empty() {
            f.push(Finding::new(ReasonCode::RecheckFailed, Scope::Compiled, format!("@[csimp] lemma {} export not closed: {missing:?}", c.thm)));
        }
        for ax in axioms_in(ex, &clo) {
            if let Some(code) = classify_axiom(&ax, allowlist, trusted_axioms) {
                f.push(Finding::new(code, Scope::Compiled, format!("@[csimp] lemma {} depends on axiom {ax} (independent export)", c.thm)));
            }
        }
        for n in &clo {
            if ex.decls.get(n).is_some_and(|d| d.is_unsafe || d.is_partial) {
                f.push(Finding::new(ReasonCode::UnapprovedAssumption, Scope::Compiled, format!("@[csimp] lemma {} uses unsafe/partial `{n}`", c.thm)));
            }
        }
    }
    f
}
