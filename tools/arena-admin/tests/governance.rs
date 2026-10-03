use arena_admin::challenge_file::{
    check_supersession, load_definition, sign_and_write, tree_digest, verify_file,
};
use arena_admin::policy::check_definition;
use arena_admin::{GovernedSet, Keypair, PublicKey};
use arena_types::challenge::{ChallengeDefinition, Tier};
use arena_types::security::{Assumption, Privacy, SecurityProfile};
use arena_types::{Digest, ObligationId};
use std::fs;
use std::path::{Path, PathBuf};

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

fn gov() -> GovernedSet {
    GovernedSet::load(&repo().join("security")).expect("governed files load")
}

fn demo_def() -> ChallengeDefinition {
    load_definition(&repo().join("challenges/drafts/demo-toy-arithmetic.draft.json")).unwrap()
}

fn local_pub() -> PublicKey {
    PublicKey::load(&repo().join("challenges/governance-local.pub")).unwrap()
}

fn dev_pub() -> PublicKey {
    PublicKey::load(&repo().join("challenges/governance-dev.pub")).unwrap()
}

/// A definition that satisfies the formal-tier policy (non-zero digests,
/// pinned assumptions, baselines). Uses an in-memory governed set whose
/// assumptions carry digests.
fn formal_fixture() -> (ChallengeDefinition, GovernedSet) {
    let mut g = gov();
    for a in g.assumptions.values_mut() {
        a.lean_decl_digest = Some(Digest::of_bytes(a.lean_decl.as_bytes()));
    }
    let mut d = demo_def();
    d.tier = Tier::Formal;
    let some = Digest::of_bytes(b"x");
    d.runtime_config_digest = some.clone();
    d.toolchain_policy.checker_image = some.clone();
    d.workload_suite.heldout_commitment = some;
    d.workload_suite.baseline_ns = vec![("toy-small".into(), 1000), ("toy-large".into(), 2000)];
    d.toolchain_policy.recheckers = vec!["lean4checker".into(), "nanoda".into()];
    d.required_obligations = arena_admin::policy::required_for(Tier::Formal, Privacy::ValidityOnly);
    d.formal_params = Some(arena_types::FormalParams {
        verify_fuel: 1 << 20,
        max_proof_bytes: d.resource_limits.max_proof_bytes,
        max_reduction_fuel: 1 << 20,
    });
    (d, g)
}

// ---------------------------------------------------------------- governed files

#[test]
fn all_governed_files_load_via_arena_types() {
    let root = repo().join("security");
    let mut n = 0;
    for sub in ["profiles", "assumptions"] {
        for e in fs::read_dir(root.join(sub)).unwrap() {
            let p = e.unwrap().path();
            if p.extension().and_then(|x| x.to_str()) != Some("json") {
                continue;
            }
            let text = fs::read_to_string(&p).unwrap();
            if sub == "profiles" {
                serde_json::from_str::<SecurityProfile>(&text)
                    .unwrap_or_else(|e| panic!("{p:?}: {e}"));
            } else {
                serde_json::from_str::<Assumption>(&text).unwrap_or_else(|e| panic!("{p:?}: {e}"));
            }
            n += 1;
        }
    }
    assert!(n >= 4);
    let g = gov();
    assert!(g.profiles.contains_key("validity-classical-128"));
    assert!(g.profiles.contains_key("zk-classical-128"));
    assert_eq!(
        g.profiles["zk-classical-128"].privacy,
        Privacy::ZeroKnowledge
    );
    assert_eq!(
        g.profiles["validity-classical-128"].privacy,
        Privacy::ValidityOnly
    );
    assert!(g.assumptions.contains_key("sha256-collision-resistance"));
}

#[test]
fn unknown_field_in_governed_file_is_rejected() {
    let t = tempfile::tempdir().unwrap();
    for sub in ["profiles", "assumptions"] {
        fs::create_dir_all(t.path().join(sub)).unwrap();
        for e in fs::read_dir(repo().join("security").join(sub)).unwrap() {
            let p = e.unwrap().path();
            fs::copy(&p, t.path().join(sub).join(p.file_name().unwrap())).unwrap();
        }
    }
    assert!(GovernedSet::load(t.path()).is_ok());
    let p = t.path().join("profiles/zk-classical-128.json");
    let mut v: serde_json::Value = serde_json::from_str(&fs::read_to_string(&p).unwrap()).unwrap();
    v["security_bits_claimed"] = 256.into();
    fs::write(&p, v.to_string()).unwrap();
    assert!(GovernedSet::load(t.path()).is_err());
}

#[test]
fn profile_referencing_ungoverned_assumption_is_rejected() {
    let t = tempfile::tempdir().unwrap();
    fs::create_dir_all(t.path().join("profiles")).unwrap();
    fs::create_dir_all(t.path().join("assumptions")).unwrap();
    let mut prof = gov().profiles["validity-classical-128"].clone();
    prof.allowed_assumptions
        .push("my-favourite-assumption".into());
    fs::write(
        t.path().join("profiles/validity-classical-128.json"),
        serde_json::to_string(&prof).unwrap(),
    )
    .unwrap();
    assert!(GovernedSet::load(t.path()).is_err());
}

// ---------------------------------------------------------------- committed challenges

#[test]
fn committed_challenges_verify() {
    let dir = repo().join("challenges");
    let g = gov();
    let mut n = 0;
    for e in fs::read_dir(&dir).unwrap() {
        let p = e.unwrap().path();
        let name = p.file_name().unwrap().to_str().unwrap().to_string();
        if name.starts_with("chl_") && name.ends_with(".json") {
            // Formal challenges must verify under the non-dev local operator key alone;
            // everything else under one of the repo keys.
            let v = verify_file(&p, &[dev_pub(), local_pub()], &g)
                .unwrap_or_else(|e| panic!("{name}: {e:#}"));
            if v.def.tier == Tier::Formal {
                verify_file(&p, &[local_pub()], &g).unwrap_or_else(|e| {
                    panic!("{name}: formal challenge not signed by the non-dev key: {e:#}")
                });
                assert!(
                    verify_file(&p, &[dev_pub()], &g).is_err(),
                    "dev key must never sign formal"
                );
            }
            n += 1;
        }
    }
    assert!(n >= 1, "expected the demo challenge to be committed");
}

#[test]
fn draft_matches_committed_demo_challenge() {
    let d = demo_def();
    let id = d.id().unwrap();
    assert!(
        repo()
            .join("challenges")
            .join(format!("{id}.json"))
            .exists(),
        "re-sign the demo after editing the draft"
    );
    assert_eq!(d.tier, Tier::Demo);
    assert!(d
        .semantic_scope
        .restrictions
        .iter()
        .any(|r| r.id == "not-near-semantics"));
}

#[test]
fn template_has_exactly_the_contract_fields() {
    fn keys(v: &serde_json::Value, prefix: &str, out: &mut Vec<String>) {
        if let Some(m) = v.as_object() {
            for (k, x) in m {
                let p = format!("{prefix}/{k}");
                out.push(p.clone());
                keys(x, &p, out);
            }
        }
    }
    let mut t: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(
            repo().join("challenges/templates/near-transfer-receipt-v1.template.json"),
        )
        .unwrap(),
    )
    .unwrap();
    t.as_object_mut().unwrap().remove("_template_notice");
    let d = serde_json::to_value(demo_def()).unwrap();
    let (mut a, mut b) = (vec![], vec![]);
    keys(&t, "", &mut a);
    keys(&d, "", &mut b);
    a.sort();
    b.sort();
    // array-element objects (classes, restrictions) are not visited, top-level
    // and nested struct fields must match exactly.
    assert_eq!(a, b);
}

// ---------------------------------------------------------------- tamper detection

fn signed_copy() -> (tempfile::TempDir, PathBuf, Keypair) {
    let t = tempfile::tempdir().unwrap();
    let kp = Keypair::generate(true, "test");
    let (ident, _) = sign_and_write(&demo_def(), &kp, &gov(), t.path()).unwrap();
    let p = t.path().join(format!("{}.json", ident.id));
    (t, p, kp)
}

fn pk(kp: &Keypair) -> PublicKey {
    PublicKey::parse(&serde_json::to_string(&kp.public_file()).unwrap()).unwrap()
}

#[test]
fn sign_then_verify_roundtrip_and_immutability() {
    let (t, p, kp) = signed_copy();
    verify_file(&p, &[pk(&kp)], &gov()).unwrap();
    // wrong key
    assert!(verify_file(&p, &[dev_pub()], &gov()).is_err());
    // cannot overwrite
    assert!(sign_and_write(&demo_def(), &kp, &gov(), t.path()).is_err());
}

#[test]
fn modified_field_breaks_id() {
    let (_t, p, kp) = signed_copy();
    let mut v: serde_json::Value = serde_json::from_str(&fs::read_to_string(&p).unwrap()).unwrap();
    v["resource_limits"]["max_verify_ms"] = 999_999.into();
    fs::write(&p, serde_json::to_string_pretty(&v).unwrap()).unwrap();
    let e = verify_file(&p, &[pk(&kp)], &gov()).unwrap_err();
    assert!(
        format!("{e:#}").contains("does not match file name"),
        "{e:#}"
    );
}

#[test]
fn modified_signature_fails() {
    let (_t, p, kp) = signed_copy();
    let sp = p.with_extension("sig");
    let mut s = fs::read_to_string(&sp).unwrap();
    let c = if s.starts_with('0') { "1" } else { "0" };
    s.replace_range(0..1, c);
    fs::write(&sp, s).unwrap();
    assert!(verify_file(&p, &[pk(&kp)], &gov()).is_err());
}

#[test]
fn omitted_optional_field_is_not_normal_form() {
    let (_t, p, kp) = signed_copy();
    let mut v: serde_json::Value = serde_json::from_str(&fs::read_to_string(&p).unwrap()).unwrap();
    v.as_object_mut().unwrap().remove("supersedes");
    fs::write(&p, serde_json::to_string_pretty(&v).unwrap()).unwrap();
    assert!(verify_file(&p, &[pk(&kp)], &gov()).is_err());
}

#[test]
fn unknown_field_in_challenge_is_rejected() {
    let (_t, p, kp) = signed_copy();
    let mut v: serde_json::Value = serde_json::from_str(&fs::read_to_string(&p).unwrap()).unwrap();
    v["security_profile"]["security_bits"] = 128.into();
    fs::write(&p, serde_json::to_string_pretty(&v).unwrap()).unwrap();
    assert!(verify_file(&p, &[pk(&kp)], &gov()).is_err());
}

// ---------------------------------------------------------------- policy

fn errs(d: &ChallengeDefinition, g: &GovernedSet) -> Vec<String> {
    check_definition(d, g).errors
}

#[test]
fn formal_fixture_passes_policy() {
    let (d, g) = formal_fixture();
    assert_eq!(errs(&d, &g), Vec::<String>::new());
}

#[test]
fn formal_tier_baselines_all_or_nothing() {
    let (mut d, g) = formal_fixture();
    d.workload_suite.baseline_ns.clear();
    assert_eq!(
        errs(&d, &g),
        Vec::<String>::new(),
        "unmeasured baseline is allowed (scores null)"
    );
    let (mut d, g) = formal_fixture();
    d.workload_suite.baseline_ns.truncate(1);
    assert!(errs(&d, &g)
        .iter()
        .any(|e| e.contains("baseline_ns does not cover")));
}

#[test]
fn formal_tier_requires_consistent_formal_params() {
    let (mut d, g) = formal_fixture();
    d.formal_params = None;
    assert!(errs(&d, &g).iter().any(|e| e.contains("formal_params")));
    let (mut d, g) = formal_fixture();
    d.formal_params.as_mut().unwrap().max_proof_bytes += 1;
    assert!(errs(&d, &g).iter().any(|e| e.contains("max_proof_bytes")));
}

#[test]
fn formal_tier_requires_every_formal_obligation() {
    let (mut d, g) = formal_fixture();
    d.required_obligations
        .retain(|o| *o != ObligationId::FormalCryptoSoundness);
    assert!(errs(&d, &g)
        .iter()
        .any(|e| e.contains("FormalCryptoSoundness")));
    let (mut d, g) = formal_fixture();
    d.required_obligations
        .retain(|o| *o != ObligationId::AxiomAudit);
    assert!(!errs(&d, &g).is_empty());
}

#[test]
fn validity_only_needs_formal_zk_not_applicable() {
    let (mut d, g) = formal_fixture();
    d.not_applicable_gates.clear();
    assert!(errs(&d, &g)
        .iter()
        .any(|e| e.contains("FORMAL_ZK must be listed")));
    let (mut d, g) = formal_fixture();
    d.required_obligations.push(ObligationId::FormalZk);
    assert!(!errs(&d, &g).is_empty());
}

#[test]
fn zk_profile_requires_formal_zk() {
    let (mut d, g) = formal_fixture();
    d.security_profile = g.profiles["zk-classical-128"].clone();
    assert!(
        !errs(&d, &g).is_empty(),
        "FORMAL_ZK N/A under zk profile must fail"
    );
    d.not_applicable_gates.clear();
    assert!(errs(&d, &g).iter().any(|e| e.contains("FormalZk")));
    d.required_obligations.push(ObligationId::FormalZk);
    assert_eq!(errs(&d, &g), Vec::<String>::new());
}

#[test]
fn only_formal_zk_may_be_not_applicable() {
    let (mut d, g) = formal_fixture();
    d.not_applicable_gates.push(ObligationId::AdversarialProofs);
    assert!(!errs(&d, &g).is_empty());
}

#[test]
fn weights_must_sum_to_one_million() {
    let (mut d, g) = formal_fixture();
    d.workload_suite.classes[0].weight_ppm += 1;
    assert!(errs(&d, &g).iter().any(|e| e.contains("1000000")));
}

#[test]
fn profile_must_match_governed_file() {
    let (mut d, g) = formal_fixture();
    d.security_profile.max_hash_queries_log2 = 40;
    assert!(errs(&d, &g)
        .iter()
        .any(|e| e.contains("differs from governed")));
    let (mut d, g) = formal_fixture();
    d.security_profile.id = "validity-classical-80".into();
    assert!(!errs(&d, &g).is_empty());
}

#[test]
fn forbidden_axioms_rejected() {
    let (mut d, g) = formal_fixture();
    d.toolchain_policy
        .axiom_allowlist
        .push("Lean.ofReduceBool".into());
    assert!(!errs(&d, &g).is_empty());
    let (mut d, g) = formal_fixture();
    d.toolchain_policy
        .axiom_allowlist
        .push("ArenaCore.Assumptions.Sha256CollisionResistant".into());
    assert!(!errs(&d, &g).is_empty(), "assumptions must never be axioms");
}

#[test]
fn formal_needs_pinned_assumptions_and_real_digests() {
    let (d, mut g) = formal_fixture();
    // the repo governed set is pinned (lean_decl_digest from decl-hash) ...
    assert!(gov()
        .assumptions
        .values()
        .all(|a| a.lean_decl_digest.is_some()));
    assert!(!errs(&d, &gov())
        .iter()
        .any(|e| e.contains("lean_decl_digest")));
    // ... and an unpinned assumption blocks the formal tier
    for a in g.assumptions.values_mut() {
        a.lean_decl_digest = None;
    }
    assert!(errs(&d, &g).iter().any(|e| e.contains("lean_decl_digest")));
    let (mut d, g) = formal_fixture();
    d.runtime_config_digest = arena_admin::policy::zero_digest();
    assert!(!errs(&d, &g).is_empty());
}

#[test]
fn dev_key_cannot_sign_formal() {
    let (d, g) = formal_fixture();
    let t = tempfile::tempdir().unwrap();
    let dev = Keypair::generate(true, "dev");
    assert!(sign_and_write(&d, &dev, &g, t.path()).is_err());
    let prod = Keypair::generate(false, "prod");
    let (ident, _) = sign_and_write(&d, &prod, &g, t.path()).unwrap();
    let p = t.path().join(format!("{}.json", ident.id));
    verify_file(&p, &[pk(&prod)], &g).unwrap();
}

// ---------------------------------------------------------------- supersede

#[test]
fn supersession_rules() {
    let old = demo_def();
    let old_id = old.id().unwrap();
    let mut new = old.clone();
    new.supersedes = Some(old_id.clone());
    new.created_at = "2026-11-01T00:00:00Z".into();
    new.workload_suite.revision = "r2".into();
    assert!(check_supersession(&old, &old_id, &new, false).ok());
    assert!(check_definition(&new, &gov()).ok());
    assert_ne!(new.id().unwrap(), old_id);

    let mut stale = new.clone();
    stale.created_at = old.created_at.clone();
    assert!(!check_supersession(&old, &old_id, &stale, false).ok());

    let mut down = new.clone();
    down.protocol_version = old.protocol_version - 1;
    assert!(!check_supersession(&old, &old_id, &down, false).ok());
    assert!(check_supersession(&old, &old_id, &down, true).ok());

    let mut wrong = new.clone();
    wrong.supersedes = Some(format!("chl_{}", "a".repeat(32)));
    assert!(!check_supersession(&old, &old_id, &wrong, false).ok());
}

// ---------------------------------------------------------------- keys

#[test]
fn private_key_handling() {
    let t = tempfile::tempdir().unwrap();
    let kp = Keypair::generate(true, "t");
    let p = t.path().join("k.key");
    kp.write_private(&p, true).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(
            fs::metadata(&p).unwrap().permissions().mode() & 0o777,
            0o600
        );
        let back = Keypair::load_private(&p).unwrap();
        assert_eq!(back.public_file(), kp.public_file());
        fs::set_permissions(&p, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(
            Keypair::load_private(&p).is_err(),
            "group/other readable key must be refused"
        );
    }
    // refuses to overwrite
    assert!(kp.write_private(&p, true).is_err());
    // refuses to write inside the repository
    assert!(kp
        .write_private(&repo().join("challenges/should-not-exist.key"), false)
        .is_err());
    assert!(!repo().join("challenges/should-not-exist.key").exists());
}

#[test]
fn committed_dev_pubkey_is_labelled_dev_only() {
    let k = dev_pub();
    assert!(k.file.dev_only);
    assert!(k.file.label.contains("DEV-ONLY"));
}

// ---------------------------------------------------------------- tree digest

#[test]
fn tree_digest_is_deterministic_and_rejects_symlinks() {
    let t = tempfile::tempdir().unwrap();
    fs::create_dir_all(t.path().join("a/b")).unwrap();
    fs::write(t.path().join("a/b/x"), b"1").unwrap();
    fs::write(t.path().join("y"), b"2").unwrap();
    let d1 = tree_digest(t.path()).unwrap();
    assert_eq!(d1, tree_digest(t.path()).unwrap());
    fs::write(t.path().join("y"), b"3").unwrap();
    assert_ne!(d1, tree_digest(t.path()).unwrap());
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink("/etc/passwd", t.path().join("evil")).unwrap();
        assert!(tree_digest(t.path()).is_err());
    }
}
