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
pub const NATIVE_AXIOMS: &[&str] = &["Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"];

/// Classify one axiom in the certificate's closure.
pub fn classify_axiom(name: &str, allowlist: &[String], trusted_axioms: &BTreeSet<String>) -> Option<ReasonCode> {
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
        f.push(Finding::new(code, Scope::All, format!("joint import of expected statement and candidate failed: {e}")));
        return f;
    }
    if let Some(fatal) = &a.fatal {
        f.push(Finding::unknown(ReasonCode::InfraError, format!("audit: {fatal}")));
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
            format!("expected statement depends on non-trusted declarations: {:?}", a.untrusted_in_statement),
        ));
    }
    if a.certificate_found != Some(true) {
        f.push(Finding::new(ReasonCode::CertificateMissing, Scope::All, "certificate constant not found".into()));
        return f;
    }
    if a.certificate_origin.as_deref() != Some("candidate") {
        f.push(Finding::new(
            ReasonCode::CertificateMissing,
            Scope::All,
            format!("certificate is not declared in a candidate module (origin {:?})", a.certificate_origin),
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
            f.push(Finding::new(code, Scope::Certificate, format!("certificate depends on axiom {ax}")));
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
            f.push(Finding::new(ReasonCode::NativeEvalFound, Scope::Certificate, format!("certified path uses unsafe `{}`", c.name)));
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
}

fn axioms_in(ex: &Export, names: &BTreeSet<String>) -> BTreeSet<String> {
    names
        .iter()
        .filter(|n| ex.decls.get(*n).is_some_and(|d| d.kind == DeclKind::Axiom))
        .cloned()
        .collect()
}

pub fn nd_audit(cand: &Export, reference: &Export, certificate: &str, expected_decl: &str, n_conjuncts: usize) -> NdAudit {
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
    let Some(cert) = cand.decls.get(certificate) else { return a };
    a.certificate_found = true;
    a.certificate_kind = Some(cert.kind);
    let Some(exp) = reference.decls.get(expected_decl) else { return a };
    let Some(exp_val) = exp.value else { return a };
    // (a) syntactic equality after positional renaming of universe params.
    if cert.level_params.len() == exp.level_params.len() {
        let subst: HashMap<String, String> =
            cert.level_params.iter().cloned().zip(exp.level_params.iter().cloned()).collect();
        let ct = cand.expr_hash(cert.ty, Some(&subst));
        a.type_equal = ct == reference.expr_hash(exp_val, None);
        if !a.type_equal {
            if let Some((n, us)) = cand.const_head(cert.ty) {
                let lv_ok = us.len() == exp.level_params.len()
                    && us.iter().zip(&cert.level_params).all(|(u, p)| cand.level_is_param(*u, p))
                    && cert.level_params.iter().zip(&exp.level_params).all(|(c, e)| c == e);
                if n == expected_decl && lv_ok && cand.decls.get(expected_decl).is_some_and(|d| {
                    ref_hash.get(expected_decl) == Some(&cand.decl_hash(d))
                }) {
                    a.type_equal = true;
                    a.type_via_expected_const = true;
                }
            }
        }
    }
    // Statement closure in the reference must be present in the candidate export.
    let mut stmt_consts = BTreeSet::new();
    reference.consts_in(exp_val, &mut Default::default(), &mut stmt_consts);
    let (stmt_closure, _) = reference.closure(stmt_consts);
    if a.type_equal {
        a.missing_trusted = stmt_closure.iter().filter(|n| !cand.decls.contains_key(*n)).cloned().collect();
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
    a.closure_digest = Some(json_digest(&a.closure.iter().map(|(n, k, h)| (n, format!("{k:?}"), h)).collect::<Vec<_>>()));
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
    if !a.shadowed.is_empty() {
        f.push(Finding::new(
            ReasonCode::ShadowedDefinition,
            Scope::All,
            format!("candidate environment redefines {} judge-pinned declaration(s): {:?}", a.shadowed.len(), &a.shadowed[..a.shadowed.len().min(10)]),
        ));
    }
    if !a.certificate_found {
        f.push(Finding::new(ReasonCode::CertificateMissing, Scope::All, "certificate not present in the exported environment".into()));
        return f;
    }
    if !a.type_equal {
        f.push(Finding::new(ReasonCode::TheoremTypeMismatch, Scope::All, "exported certificate type is not structurally equal to the reference statement".into()));
    }
    if !a.missing_trusted.is_empty() || !a.closure_missing.is_empty() {
        f.push(Finding::new(
            ReasonCode::RecheckFailed,
            Scope::All,
            format!("export is not closed: missing {:?} {:?}", a.missing_trusted, a.closure_missing),
        ));
    }
    match &a.conjunct_axioms {
        Some(per) => {
            for (i, axs) in per.iter().enumerate() {
                for ax in axs {
                    if let Some(code) = classify_axiom(ax, allowlist, &a.trusted_axioms) {
                        f.push(Finding::new(code, Scope::Conjunct(i), format!("conjunct {i} depends on axiom {ax}")));
                    }
                }
            }
        }
        None => {
            for ax in &a.axioms {
                if let Some(code) = classify_axiom(ax, allowlist, &a.trusted_axioms) {
                    f.push(Finding::new(code, Scope::Certificate, format!("certificate depends on axiom {ax}")));
                }
            }
        }
    }
    for n in &a.unsafe_or_partial {
        f.push(Finding::new(ReasonCode::UnapprovedAssumption, Scope::Certificate, format!("certified path uses unsafe/partial `{n}`")));
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
        diffs.push(format!("type_equal lean={:?} ndjson={}", lean.type_equal, nd.type_equal));
    }
    if lean_axioms != nd.axioms {
        diffs.push(format!("axioms lean={lean_axioms:?} ndjson={:?}", nd.axioms));
    }
    (!diffs.is_empty()).then(|| {
        Finding::new(ReasonCode::RecheckFailed, Scope::All, format!("independent audits disagree: {}", diffs.join("; ")))
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
        let d = std::env::temp_dir().join(format!("fc-audit-{}-{:?}", std::process::id(), std::thread::current().id()));
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
        let good = write(&d, "good.ndjson", &[DEF_P, r#"{"thm":{"all":[5],"levelParams":[],"name":5,"type":2,"value":4}}"#]);
        let a = nd_audit(&good, &reference, "Candidate.certificate", "ArenaExpected.expectedType", 1);
        assert!(a.certificate_found && a.type_equal && a.shadowed.is_empty() && a.missing_trusted.is_empty(), "{a:?}");
        assert!(nd_findings(&a, &["propext".into()]).is_empty());

        // Same name `P`, different body: statement matches by name but P is shadowed.
        let shadow = write(&d, "shadow.ndjson", &[DEF_P_ALTERED, r#"{"thm":{"all":[5],"levelParams":[],"name":5,"type":2,"value":4}}"#]);
        let a = nd_audit(&shadow, &reference, "Candidate.certificate", "ArenaExpected.expectedType", 1);
        assert_eq!(a.shadowed, vec!["P".to_string()]);
        assert!(nd_findings(&a, &[]).iter().any(|f| f.code == ReasonCode::ShadowedDefinition));

        // Wrong type (Prop instead of P).
        let wrong = write(&d, "wrong.ndjson", &[DEF_P, r#"{"thm":{"all":[5],"levelParams":[],"name":5,"type":0,"value":4}}"#]);
        let a = nd_audit(&wrong, &reference, "Candidate.certificate", "ArenaExpected.expectedType", 1);
        assert!(!a.type_equal);

        // Missing certificate.
        let a = nd_audit(&good, &reference, "Candidate.nope", "ArenaExpected.expectedType", 1);
        assert!(nd_findings(&a, &[]).iter().any(|f| f.code == ReasonCode::CertificateMissing));

        // Axiom in the closure: candidate-declared axiom used by the certificate.
        let ax = write(&d, "ax.ndjson", &[
            DEF_P,
            r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":9,"type":2}}"#,
            r#"{"const":{"name":9,"us":[]},"ie":6}"#,
            r#"{"thm":{"all":[5],"levelParams":[],"name":5,"type":2,"value":6}}"#,
        ]);
        let a = nd_audit(&ax, &reference, "Candidate.certificate", "ArenaExpected.expectedType", 1);
        assert!(a.type_equal);
        assert_eq!(a.axioms.iter().cloned().collect::<Vec<_>>(), vec!["cheat".to_string()]);
        assert!(nd_findings(&a, &["propext".into()]).iter().any(|f| f.code == ReasonCode::ForbiddenAxiom));
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
        std::fs::write(&p, format!("{META}\n{{\"in\":1,\"str\":{{\"pre\":5,\"str\":\"x\"}}}}\n")).unwrap();
        assert!(Export::read(&p, 1 << 20).is_err(), "forward name reference");
        std::fs::write(&p, format!("{META}\n{}\n{}\n{DEF_P}\n{DEF_P}\n", names(), exprs())).unwrap();
        assert!(Export::read(&p, 1 << 20).is_err(), "duplicate declaration");
        std::fs::write(&p, format!("{}\n{}\n", names(), exprs())).unwrap();
        assert!(Export::read(&p, 1 << 20).is_err(), "missing meta");
        std::fs::write(&p, format!("{META}\n{{\"ie\":0,\"natVal\":\"12a\"}}\n")).unwrap();
        assert!(Export::read(&p, 1 << 20).is_err(), "bad nat literal");
        assert!(Export::read(&p, 1).is_err(), "size cap");
    }

    #[test]
    fn axiom_classification() {
        let allow: Vec<String> = vec!["propext".into(), "Quot.sound".into(), "Classical.choice".into()];
        let trusted: BTreeSet<String> = ["ArenaCore.Assumptions.cr".to_string()].into();
        assert_eq!(classify_axiom("propext", &allow, &trusted), None);
        assert_eq!(classify_axiom("sorryAx", &allow, &trusted), Some(ReasonCode::SorryFound));
        assert_eq!(classify_axiom("Lean.ofReduceBool", &allow, &trusted), Some(ReasonCode::NativeEvalFound));
        assert_eq!(classify_axiom("C.cert._native.native_decide.ax_1_1", &allow, &trusted), Some(ReasonCode::NativeEvalFound));
        assert_eq!(classify_axiom("ArenaCore.Assumptions.cr", &allow, &trusted), Some(ReasonCode::UnapprovedAssumption));
        assert_eq!(classify_axiom("Candidate.cheat", &allow, &trusted), Some(ReasonCode::ForbiddenAxiom));
    }
}
