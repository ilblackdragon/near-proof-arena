//! v3 D0 (`near-chunk-validation-d0`, `near-arena-claim-v3`) end to end
//! through the worker stages with the reference candidate
//! `examples/reexec-v3-d0` (native-lean route): VALIDATE, BUILD,
//! FORMAL_CHECK against the challenge's frozen trusted tree and the v3
//! Expected template, CONFORMANCE (pinned arena-layout public fixtures,
//! judge-sampled cases of every class from `near-arena-oracle-v3`, the
//! committed held-out set when given, and the **rejection cases**: nearcore
//! rejects or out of D0 — the candidate must never get one accepted),
//! ADVERSARIAL, BENCHMARK.
//!
//! `reference_all_stages`: bwrap-dev (job tier demo; the pipeline is
//! identical). `reference_firecracker`: every stage in Firecracker microVMs
//! with the lean-checker image (checker identity re-pinned to that image,
//! test-only), VMs on CPUs 8-15 / 24-31 only.
//!
//! The challenge is the unsigned draft (`challenges/drafts/near-chunk-
//! validation-d0.draft.json`); the worker trusts the job's definition
//! (signatures are server-side). Opt-in: `ARENA_NEAR_TESTS=1`,
//! `ARENA_NEAR_ORACLE_V3` (default `oracle/v3/target/debug/near-arena-oracle-v3`),
//! `ARENA_V3_TRUSTED_COMMIT` (default `HEAD`: the commit whose `formal-core/` +
//! `spec/lean/` the draft pins), optional `ARENA_TEST_HELDOUT_V3` (held-out dir).

mod common;

use arena_jobs::*;
use arena_sandbox::Mount;
use arena_types::{ChallengeDefinition, GateStatus, ObligationId, VerifiedSurface};
use arena_worker::executor::{BuildEnv, FormalEnv, JobExecutor};
use arena_worker::oracle::Oracles;
use common::*;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;

const DRAFT: &str = "challenges/drafts/near-chunk-validation-d0.draft.json";
const CANDIDATE: &str = "examples/reexec-v3-d0";

fn git_files(rel: &str) -> std::collections::BTreeMap<String, (u32, Vec<u8>)> {
    let out = std::process::Command::new("git")
        .arg("-C")
        .arg(repo())
        .args(["ls-files", "-s", "--", rel])
        .output()
        .unwrap();
    let mut m = std::collections::BTreeMap::new();
    for l in String::from_utf8(out.stdout).unwrap().lines() {
        let (meta, path) = l.split_once('\t').unwrap();
        let mode = if meta.starts_with("100755") {
            0o755
        } else {
            0o644
        };
        m.insert(
            path.strip_prefix(&format!("{rel}/")).unwrap().to_string(),
            (mode, std::fs::read(repo().join(path)).unwrap()),
        );
    }
    m
}

fn export(rel: &str, dest: &Path) -> PathBuf {
    for (p, (_, b)) in git_files(rel) {
        let d = dest.join(rel).join(p);
        std::fs::create_dir_all(d.parent().unwrap()).unwrap();
        std::fs::write(d, b).unwrap();
    }
    dest.join(rel)
}

fn cpus(a: u32, b: u32) -> Vec<u32> {
    (a..=b).collect()
}

fn v3_env(f: &mut Fixture) -> Option<()> {
    if std::env::var("ARENA_NEAR_TESTS").as_deref() != Ok("1") {
        skip_gated!("set ARENA_NEAR_TESTS=1");
        return None;
    }
    let oracle = std::env::var_os("ARENA_NEAR_ORACLE_V3")
        .map(PathBuf::from)
        .unwrap_or_else(|| repo().join("oracle/v3/target/debug/near-arena-oracle-v3"));
    if !oracle.is_file() {
        skip_gated!("no near-arena-oracle-v3 at {}", oracle.display());
        return None;
    }
    let home = PathBuf::from(std::env::var("HOME").unwrap());
    f.exec.ctx.build = BuildEnv {
        mounts: vec![
            Mount {
                host: home.join(".rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu"),
                guest: "/opt/rust".into(),
            },
            Mount {
                host: home.join(".elan/toolchains/leanprover--lean4---v4.34.1"),
                guest: "/opt/lean".into(),
            },
        ],
        path: Some("/opt/rust/bin:/opt/lean/bin:/usr/bin:/bin".into()),
        env: vec![],
        images_dir: None,
        toolchain_image: None,
    };
    let mut o = Oracles::builtin()
        .with_near_v3(
            oracle,
            &[repo().join("spec/workloads/near-chunk-validation-d0")],
        )
        .unwrap();
    let clean = f.tmp.path().join("clean");
    let fx = o
        .add_fixtures_dir(&export("oracle/fixtures/v3/arena-public", &clean))
        .unwrap();
    if let Some(h) = std::env::var_os("ARENA_TEST_HELDOUT_V3") {
        o.add_heldout_dir(Path::new(&h)).unwrap();
    }
    f.exec.ctx.oracles = o;
    f.chal =
        serde_json::from_slice::<ChallengeDefinition>(&std::fs::read(repo().join(DRAFT)).unwrap())
            .unwrap();
    assert_eq!(f.chal.claim_encoding.format, "near-arena-claim-v3");
    assert_eq!(fx, f.chal.workload_suite.public_fixtures, "v3 fixture pin");
    let commit = std::env::var("ARENA_V3_TRUSTED_COMMIT").unwrap_or_else(|_| "HEAD".into());
    let store = frozen_store(f.tmp.path(), &f.chal, &commit)?;
    f.exec.ctx.formal = Some(FormalEnv {
        trusted_trees: Some(store),
        configs_dir: repo().join("runners/formal-checker/challenges"),
        images_dir: None,
    });
    f.exec.ctx.bench_batch_cap = Some(2);
    f.exec.ctx.conformance_samples = 3;
    f.exec.ctx.run_cpus = Some(cpus(8, 15));
    f.exec.ctx.bench_cpus = Some(cpus(24, 31));
    f.chal.toolchain_policy.checker_image = arena_formal_checker::toolchain::ToolPaths::discover()
        .unwrap()
        .image_digest()
        .unwrap();
    Some(())
}

fn challenge_id(f: &Fixture) -> String {
    f.chal.id().unwrap()
}

fn ctx(f: &Fixture, pkg: &arena_types::Digest) -> JobContext {
    let mut c = f.ctx(pkg);
    c.challenge_id = challenge_id(f);
    c.challenge_digest = f.chal.digest().unwrap();
    c.tier = arena_types::challenge::Tier::Demo;
    c
}

/// The candidate's tracked files with `candidate.toml` naming this test's
/// challenge id (the committed manifest names the signed challenge).
fn package(f: &Fixture) -> std::collections::BTreeMap<String, (u32, Vec<u8>)> {
    let mut files = git_files(CANDIDATE);
    let (mode, toml) = files.remove("candidate.toml").unwrap();
    let toml = String::from_utf8(toml).unwrap();
    let toml: String = toml
        .lines()
        .map(|l| {
            if l.starts_with("challenge = ") {
                format!("challenge = \"{}\"", challenge_id(f))
            } else {
                l.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    files.insert("candidate.toml".into(), (mode, toml.into_bytes()));
    files
}

fn run(f: &Fixture, spec: JobSpec) -> JobResult {
    let t = std::time::Instant::now();
    let kind = spec.kind();
    let r = f
        .exec
        .execute(&spec, "near-v3", &AtomicBool::new(false))
        .unwrap();
    eprintln!("{kind}: {:?}", t.elapsed());
    for g in &r.gates {
        eprintln!(
            "  {:?} {:?} {:?} {}",
            g.gate,
            g.status,
            g.reason_codes,
            &g.summary[..g.summary.len().min(700)]
        );
    }
    r
}

fn all_stages(f: &Fixture, tier: arena_types::challenge::Tier) {
    let pkg = f.put(&tar_of(&package(f)));
    let mut c = ctx(f, &pkg);
    c.tier = tier;
    let v = run(
        f,
        JobSpec::Validate(ValidateJob {
            ctx: c.clone(),
            challenge: f.chal.clone(),
        }),
    );
    assert_eq!(
        v.gates[0].status,
        GateStatus::Pass,
        "{}",
        v.gates[0].summary
    );
    let manifest = v.manifest.unwrap();
    let b = run(
        f,
        JobSpec::Build(BuildJob {
            ctx: c.clone(),
            challenge: f.chal.clone(),
            manifest: manifest.clone(),
        }),
    );
    assert_eq!(
        b.gates[0].status,
        GateStatus::Pass,
        "{}",
        b.gates[0].summary
    );
    let mut build = b.build.unwrap();
    let vs = VerifiedSurface {
        declared_tier: None,
        challenge_id: challenge_id(f),
        verify_artifact: build.verify.clone(),
        prepare_artifact: build.prepare.clone(),
        public_artifacts: build.public_artifacts.clone(),
        formal_tree: build.formal_tree.clone(),
        certificate_decl: build.certificate_decl.clone(),
        checker_image: f.chal.toolchain_policy.checker_image.clone(),
        verify_route: manifest.entry.verify_route,
        verifier_bytecode: build.verifier_bytecode.clone(),
        verifier_model: manifest
            .formal
            .as_ref()
            .and_then(|f| f.verifier_model.clone()),
        verifier_model_module: manifest
            .formal
            .as_ref()
            .and_then(|f| f.verifier_model_module.clone()),
    };
    let fc = run(
        f,
        JobSpec::FormalCheck(FormalCheckJob {
            ctx: c.clone(),
            challenge: f.chal.clone(),
            manifest: manifest.clone(),
            build: build.clone(),
            verified_surface: vs,
        }),
    );
    for g in &fc.gates {
        if g.gate != ObligationId::FormalZk {
            assert_eq!(g.status, GateStatus::Pass, "{:?}: {}", g.gate, g.summary);
        }
    }
    build.native_verifier = Some(
        fc.native_verifier
            .clone()
            .expect("judge-built native verifier"),
    );
    let job = ExecJob {
        ctx: c,
        challenge: f.chal.clone(),
        manifest,
        build,
        reference: None,
    };
    let conf = run(f, JobSpec::Conformance(job.clone()));
    for g in &conf.gates {
        assert_eq!(g.status, GateStatus::Pass, "{:?}: {}", g.gate, g.summary);
    }
    let s = &gate(&conf, ObligationId::ConformanceDifferential).summary;
    assert!(s.contains("78 public fixtures"), "{s}");
    assert!(s.contains("judge-sampled"), "{s}");
    assert!(
        s.contains("rejection case(s)") && s.contains(" 0 accepted"),
        "{s}"
    );
    let a = run(f, JobSpec::Adversarial(job.clone()));
    assert_eq!(
        a.gates[0].status,
        GateStatus::Pass,
        "{}",
        a.gates[0].summary
    );
    let r = run(f, JobSpec::Benchmark(job));
    assert_eq!(
        r.gates[0].status,
        GateStatus::Pass,
        "{}",
        r.gates[0].summary
    );
}

#[test]
fn reference_all_stages() {
    let mut f = fixture();
    if v3_env(&mut f).is_none() {
        return;
    }
    all_stages(&f, arena_types::challenge::Tier::Demo);
}

/// Overlay the hostile case `hostile` on the reference package; it must pass the
/// formal gates but fail ADVERSARIAL_PROOFS with HOSTILE_PROOF_ACCEPTED, with a
/// mutant label containing `needle`.
fn hostile_fails_adversarial(hostile: &str, needle: &str) {
    let mut f = fixture();
    if v3_env(&mut f).is_none() {
        return;
    }
    let mut files = package(&f);
    for (p, v) in git_files(hostile) {
        if ["BASE", "expect.json", "README.md"].contains(&p.as_str()) {
            continue;
        }
        files.insert(p, v);
    }
    let pkg = f.put(&tar_of(&files));
    let c = ctx(&f, &pkg);
    let v = run(
        &f,
        JobSpec::Validate(ValidateJob {
            ctx: c.clone(),
            challenge: f.chal.clone(),
        }),
    );
    let manifest = v.manifest.unwrap();
    let b = run(
        &f,
        JobSpec::Build(BuildJob {
            ctx: c.clone(),
            challenge: f.chal.clone(),
            manifest: manifest.clone(),
        }),
    );
    let mut build = b.build.unwrap();
    let vs = VerifiedSurface {
        declared_tier: None,
        challenge_id: challenge_id(&f),
        verify_artifact: build.verify.clone(),
        prepare_artifact: build.prepare.clone(),
        public_artifacts: build.public_artifacts.clone(),
        formal_tree: build.formal_tree.clone(),
        certificate_decl: build.certificate_decl.clone(),
        checker_image: f.chal.toolchain_policy.checker_image.clone(),
        verify_route: manifest.entry.verify_route,
        verifier_bytecode: build.verifier_bytecode.clone(),
        verifier_model: manifest
            .formal
            .as_ref()
            .and_then(|f| f.verifier_model.clone()),
        verifier_model_module: manifest
            .formal
            .as_ref()
            .and_then(|f| f.verifier_model_module.clone()),
    };
    let fc = run(
        &f,
        JobSpec::FormalCheck(FormalCheckJob {
            ctx: c.clone(),
            challenge: f.chal.clone(),
            manifest: manifest.clone(),
            build: build.clone(),
            verified_surface: vs,
        }),
    );
    build.native_verifier = Some(
        fc.native_verifier
            .clone()
            .expect("judge-built native verifier"),
    );
    let job = ExecJob {
        ctx: c,
        challenge: f.chal.clone(),
        manifest,
        build,
        reference: None,
    };
    let a = run(&f, JobSpec::Adversarial(job));
    let g = &a.gates[0];
    assert_eq!(g.status, GateStatus::Fail, "{}", g.summary);
    assert!(g
        .reason_codes
        .contains(&arena_types::ReasonCode::HostileProofAccepted));
    assert!(g.summary.contains(needle), "{}", g.summary);
}

/// The pre-canonical reference (proof = raw witness; hostile case
/// `adversarial/hostile-submissions/near-v3-malleable-witness`) passes the
/// formal gates and conformance but must fail ADVERSARIAL_PROOFS with
/// HOSTILE_PROOF_ACCEPTED, deterministically, via `v3-ignored-fields`.
#[test]
fn malleable_witness_reference_fails_adversarial() {
    hostile_fails_adversarial(
        "adversarial/hostile-submissions/near-v3-malleable-witness",
        "v3-ignored-fields/",
    );
}

/// The canonical-only reference (ignored fields zeroed, but the receipt-proof map and
/// every `base_state` left as the producer encoded them; hostile case
/// `adversarial/hostile-submissions/near-v3-lenient-witness`) must fail
/// ADVERSARIAL_PROOFS with HOSTILE_PROOF_ACCEPTED, deterministically, via
/// `v3-witness-freedoms` (duplicate key, reorder, injected unused value).
#[test]
fn lenient_witness_reference_fails_adversarial() {
    hostile_fails_adversarial(
        "adversarial/hostile-submissions/near-v3-lenient-witness",
        "v3-witness-freedoms/",
    );
}

/// A candidate whose verifier accepts everything passes every positive case;
/// CONFORMANCE must fail on the rejection cases (COUNTEREXAMPLE_FOUND) — the
/// rejection oracle is what catches it (the unsigned draft + bwrap-dev).
#[test]
fn accept_all_verifier_fails_on_rejection_cases() {
    let mut f = fixture();
    if v3_env(&mut f).is_none() {
        return;
    }
    let pkg = f.put(&tar_of(&package(&f)));
    let c = ctx(&f, &pkg);
    let v = run(
        &f,
        JobSpec::Validate(ValidateJob {
            ctx: c.clone(),
            challenge: f.chal.clone(),
        }),
    );
    let manifest = v.manifest.unwrap();
    let b = run(
        &f,
        JobSpec::Build(BuildJob {
            ctx: c.clone(),
            challenge: f.chal.clone(),
            manifest: manifest.clone(),
        }),
    );
    let mut build = b.build.unwrap();
    // A judge "native verifier" that accepts everything (test-only stand-in
    // for an unsound candidate verifier).
    let accept_all = f.tmp.path().join("accept-all");
    std::fs::write(&accept_all, "#!/bin/sh\nexit 0\n").unwrap();
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&accept_all, std::fs::Permissions::from_mode(0o755)).unwrap();
    let bytes = std::fs::read(&accept_all).unwrap();
    build.native_verifier = Some(f.put(&bytes));
    let job = ExecJob {
        ctx: c,
        challenge: f.chal.clone(),
        manifest,
        build,
        reference: None,
    };
    let conf = run(&f, JobSpec::Conformance(job));
    let g = gate(&conf, ObligationId::ConformanceDifferential);
    assert_eq!(g.status, GateStatus::Fail, "{}", g.summary);
    assert!(
        g.reason_codes
            .contains(&arena_types::ReasonCode::CounterexampleFound),
        "{:?}",
        g.reason_codes
    );
}

// ---------------------------------------------------------------------------------------------
// Structure-aware v3 mutators on every witness shape (D0, D1, D2, D3 code blobs). Not opt-in:
// pure byte walking over the committed oracle fixtures. The semantics check (every freedom
// mutant is accepted by the Lean relation iff the honest witness is) runs when the compiled
// checker `spec/lean/v3/.lake/build/bin/nearspec-v3-check-d2` exists (else it is skipped with a
// note); the Lean relations agree with nearcore on the oracle corpora (spec §10 difftests).

use arena_worker::mutators::{v3_freedom_mutants, v3_ignored_offsets, v3_layout, V3Layout};

/// `(case dir, claim, witness)` of every honest positive of an oracle corpus directory.
fn corpus(rel: &str) -> Vec<(PathBuf, Vec<u8>)> {
    let dir = repo().join(rel);
    let mut out = vec![];
    let Ok(rd) = std::fs::read_dir(&dir) else {
        return out;
    };
    let mut ds: Vec<_> = rd.map(|e| e.unwrap().path()).collect();
    ds.sort();
    for d in ds {
        if let Ok(w) = std::fs::read(d.join("witness.bin")) {
            out.push((d, w));
        }
    }
    out
}

fn n_values(l: &V3Layout) -> usize {
    l.main.values.len() + l.implicit.iter().map(|t| t.values.len()).sum::<usize>()
}

/// Append contract-code blobs to a witness file (the D3 `Vec<bytes> contract_code`).
fn with_codes(file: &[u8], codes: &[&[u8]]) -> Vec<u8> {
    let l = v3_layout(file).unwrap();
    let mut out = file[..l.codes_count_at].to_vec();
    out.extend_from_slice(&(codes.len() as u32).to_le_bytes());
    for c in codes {
        out.extend_from_slice(&(c.len() as u32).to_le_bytes());
        out.extend_from_slice(c);
    }
    out
}

#[test]
fn v3_walker_knows_every_d0_d1_d2_witness() {
    for rel in [
        "oracle/fixtures/v3/public/d0",
        "oracle/fixtures/v3/public-d1/d1",
        "oracle/fixtures/v3/public-d2/d2",
    ] {
        let cs = corpus(rel);
        assert!(!cs.is_empty(), "{rel}: no fixtures");
        for (d, w) in &cs {
            let l = v3_layout(w).unwrap_or_else(|| panic!("{}: not walked", d.display()));
            assert!(l.codes.is_empty());
            assert_eq!(v3_ignored_offsets(w).unwrap().len(), 3 + l.implicit.len());
            for (label, q) in v3_freedom_mutants(w) {
                assert_ne!(&q, w, "{} {label}", d.display());
                let m = v3_layout(&q)
                    .unwrap_or_else(|| panic!("{} {label}: not a witness", d.display()));
                assert!(
                    !label.starts_with("codes/"),
                    "{label} on a code-free witness"
                );
                let dv = n_values(&m) as i64 - n_values(&l) as i64;
                let de = m.entries.len() as i64 - l.entries.len() as i64;
                match label.split('/').nth(1).unwrap().split('.').next().unwrap() {
                    "duplicate-key" => assert_eq!((de, dv), (1, 0)),
                    "reorder" => assert_eq!((de, dv), (0, 0)),
                    "duplicate" | "inject-unused" => assert_eq!((de, dv), (0, 1)),
                    other => panic!("unexpected mutant {other}"),
                }
            }
        }
        eprintln!("{rel}: {} witnesses walked", cs.len());
    }
}

#[test]
fn v3_code_blob_mutants() {
    let (_, w) = corpus("oracle/fixtures/v3/public-d2/d2")
        .into_iter()
        .next()
        .unwrap();
    // one blob: duplicate + inject-unused; two distinct blobs: also reorder
    for codes in [
        vec![&b"\0asm\x01\0\0\0code-a"[..]],
        vec![&b"\0asm\x01\0\0\0code-a"[..], &b"\0asm\x01\0\0\0b"[..]],
    ] {
        let f = with_codes(&w, &codes);
        let l = v3_layout(&f).unwrap();
        assert_eq!(l.codes.len(), codes.len());
        let ms: Vec<_> = v3_freedom_mutants(&f)
            .into_iter()
            .filter(|(n, _)| n.starts_with("codes/"))
            .collect();
        let names: Vec<&str> = ms.iter().map(|(n, _)| n.as_str()).collect();
        let want: &[&str] = if codes.len() == 2 {
            &["codes/reorder", "codes/duplicate", "codes/inject-unused"]
        } else {
            &["codes/duplicate", "codes/inject-unused"]
        };
        assert_eq!(names, want);
        for (n, q) in &ms {
            let m = v3_layout(q).unwrap();
            // the state witness is untouched; only the code list changes
            assert_eq!(
                &q[m.sw_start..m.sw_start + m.sw_len],
                &f[l.sw_start..l.sw_start + l.sw_len]
            );
            let blobs = |x: &[u8], l: &V3Layout| {
                let mut v: Vec<Vec<u8>> =
                    l.codes.iter().map(|&(a, b)| x[a + 4..b].to_vec()).collect();
                v.sort();
                v
            };
            match n.as_str() {
                "codes/reorder" => assert_eq!(blobs(q, &m), blobs(&f, &l)),
                "codes/duplicate" => assert_eq!(m.codes.len(), l.codes.len() + 1),
                _ => assert_eq!(m.codes.len(), l.codes.len() + 1),
            }
        }
    }
}

/// Every freedom mutant of an accepted witness is accepted by the Lean relation as well (the
/// mutants are semantics-preserving), so only a normal-form verifier rejects them.
#[test]
fn v3_freedom_mutants_preserve_the_relation() {
    let bin = repo().join("spec/lean/v3/.lake/build/bin/nearspec-v3-check-d2");
    if !bin.exists() {
        eprintln!("skipped: {} not built", bin.display());
        return;
    }
    let tmp = tempfile::tempdir().unwrap();
    for (rel, flag) in [
        ("oracle/fixtures/v3/public/d0", "--d0"),
        ("oracle/fixtures/v3/public-d1/d1", "--d1"),
        ("oracle/fixtures/v3/public-d2/d2", ""),
    ] {
        let mut dirs = vec![];
        // a sample (every 8th case) keeps the run short; every mutant kind still occurs
        for (i, (d, w)) in corpus(rel)
            .into_iter()
            .enumerate()
            .filter(|(i, _)| i % 8 == 0)
        {
            let claim = std::fs::read(d.join("claim.bin")).unwrap();
            for (label, q) in v3_freedom_mutants(&w) {
                let m = tmp.path().join(format!(
                    "{}-{i}-{}",
                    flag.trim_start_matches('-'),
                    label.replace('/', "_")
                ));
                std::fs::create_dir_all(&m).unwrap();
                std::fs::write(m.join("claim.bin"), &claim).unwrap();
                std::fs::write(m.join("witness.bin"), &q).unwrap();
                dirs.push((d.clone(), m));
            }
        }
        assert!(!dirs.is_empty(), "{rel}: no mutants");
        let verdicts = |ds: Vec<&Path>| -> Vec<String> {
            let mut cmd = std::process::Command::new(&bin);
            if !flag.is_empty() {
                cmd.arg(flag);
            }
            let o = cmd.args(ds).output().unwrap();
            assert!(o.status.success());
            String::from_utf8(o.stdout)
                .unwrap()
                .lines()
                .map(|l| {
                    l.split("\"verdict\": \"")
                        .nth(1)
                        .unwrap()
                        .split('"')
                        .next()
                        .unwrap()
                        .to_string()
                })
                .collect()
        };
        let base = verdicts(dirs.iter().map(|(d, _)| d.as_path()).collect());
        let muts = verdicts(dirs.iter().map(|(_, m)| m.as_path()).collect());
        for ((b, m), (_, md)) in base.iter().zip(&muts).zip(&dirs) {
            assert_eq!(b, m, "{}: verdict changed", md.display());
        }
        eprintln!("{rel}: {} mutants, verdicts preserved", dirs.len());
    }
}
