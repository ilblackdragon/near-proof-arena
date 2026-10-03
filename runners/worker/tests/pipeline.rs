//! End-to-end stage tests through bwrap-dev with the toy sh candidate.
//! Run with `ARENA_DEV_UNSAFE=1`.

mod common;

use arena_types::{GateResult, GateStatus, ObligationId, ReasonCode};
use arena_worker::executor::JobExecutor;
use arena_worker::jobs::*;
use common::*;
use std::sync::atomic::AtomicBool;

fn exec(f: &Fixture, spec: JobSpec) -> JobOutput {
    f.exec
        .execute(&job("j", spec), &AtomicBool::new(false))
        .unwrap()
}

fn gate(o: &JobOutput, g: ObligationId) -> &GateResult {
    o.gates
        .iter()
        .find(|x| x.gate == g)
        .unwrap_or_else(|| panic!("no {g:?} gate in {:?}", o.gates))
}

fn assert_pass(o: &JobOutput, g: ObligationId) {
    let r = gate(o, g);
    assert_eq!(
        r.status,
        GateStatus::Pass,
        "{g:?}: {} {:?}",
        r.summary,
        r.reason_codes
    );
}

fn assert_fail(o: &JobOutput, g: ObligationId, reason: ReasonCode) {
    let r = gate(o, g);
    assert_eq!(r.status, GateStatus::Fail, "{g:?}: {}", r.summary);
    assert!(
        r.reason_codes.contains(&reason),
        "{g:?}: {:?} lacks {reason:?}; {}",
        r.reason_codes,
        r.summary
    );
}

fn conformance(f: &Fixture, bundle: &arena_types::Digest, cases: Vec<OracleCase>) -> JobOutput {
    exec(
        f,
        JobSpec::Conformance(ConformanceJob {
            bundle: bundle.clone(),
            entry: entry(),
            params: f.put(b"params-v1"),
            cases,
            limits: run_limits(),
            request_pin: None,
        }),
    )
}

#[test]
fn honest_candidate_passes_every_stage() {
    let f = fixture();
    // validate
    let pkg = f.put(&tar_of(&package_files()));
    let v = exec(
        &f,
        JobSpec::Validate(ValidateJob {
            package: pkg,
            challenge_id: CHALLENGE.into(),
        }),
    );
    assert_pass(&v, ObligationId::PkgWellformed);
    assert_eq!(v.manifest.as_ref().unwrap().name, "toy-sha");
    assert!(
        !gate(&v, ObligationId::PkgWellformed)
            .reason_codes
            .contains(&ReasonCode::DemoOnly),
        "validate runs no candidate code"
    );
    assert_eq!(v.sandbox.isolation, "bwrap-dev (DEMO-only)");
    assert_eq!(v.sandbox.tier_cap, Some(arena_types::challenge::Tier::Demo));

    // build (twice, reproducible)
    let (b, bundle) = f.build(&package_files());
    assert_pass(&b, ObligationId::BuildReproducible);
    let g = gate(&b, ObligationId::BuildReproducible);
    assert!(g.reason_codes.contains(&ReasonCode::DemoOnly));
    assert!(g.summary.starts_with("[bwrap-dev (DEMO-only)]"));
    assert!(b.artifact("toolchain_image").is_some() && b.artifact("entry_verify").is_some());
    let bundle = bundle.unwrap();

    // conformance (public + held-out cases)
    let mut cases = f.cases(2, true, claim_for);
    cases.extend(f.cases(1, false, claim_for));
    let c = conformance(&f, &bundle, cases.clone());
    for g in [
        ObligationId::ConformanceDifferential,
        ObligationId::ProverReliability,
        ObligationId::ResourceLimits,
    ] {
        assert_pass(&c, g);
    }
    let public_artifacts = c.artifact("public_artifacts").unwrap().clone();
    let honest: Vec<HonestProof> = cases
        .iter()
        .filter(|c| c.public)
        .map(|k| HonestProof {
            case_id: k.id.clone(),
            claim: c.artifact(&format!("claim:{}", k.id)).unwrap().clone(),
            proof: c.artifact(&format!("proof:{}", k.id)).unwrap().clone(),
        })
        .collect();
    let heldout = c
        .artifacts
        .iter()
        .find(|a| a.name.starts_with("proof:heldout"))
        .unwrap();
    assert!(!heldout.public);
    for g in &c.gates {
        assert!(
            !g.summary.contains("heldout-secret"),
            "held-out id leaked: {}",
            g.summary
        );
        assert!(g.evidence.iter().all(|e| !e.label.contains("heldout")));
    }

    // adversarial
    let a = exec(
        &f,
        JobSpec::Adversarial(AdversarialJob {
            bundle: bundle.clone(),
            entry: entry(),
            public_artifacts: public_artifacts.clone(),
            honest,
            mutators: vec![],
            seed: 42,
            limits: run_limits(),
        }),
    );
    assert_pass(&a, ObligationId::AdversarialProofs);
    let s = &gate(&a, ObligationId::AdversarialProofs).summary;
    assert!(s.contains(" 0 accepted") && s.contains("adv:"), "{s}");

    // benchmark
    let batch = f.cases(2, true, claim_for);
    let fresh = f.cases(3, true, claim_for)[2..].to_vec();
    let bj = BenchmarkJob {
        bundle,
        entry: entry(),
        params: f.put(b"params-v1"),
        public_artifacts: Some(public_artifacts),
        classes: vec![BenchClass {
            class_id: "small".into(),
            weight_ppm: 1_000_000,
            baseline_ns: 10_000_000_000,
            batch,
            fresh_batch: fresh,
        }],
        procedure: arena_types::challenge::MeasurementProcedure {
            warmup_runs: 1,
            measured_runs: 3,
            aggregation: "median".into(),
            outlier_mad_k: 1000,
            cold_runs: 1,
            concurrency: 1,
            per_run_timeout_ms: 20_000,
            invocation_mode: None,
        },
        hardware_profile: "dev-host".into(),
        suite_revision: "r1".into(),
        schedule_seed: 7,
        bootstrap_seed: 9,
        bootstrap_iterations: 200,
        limits: run_limits(),
        request_pin: None,
    };
    // bench-spec-v1.1: one sandbox instance per batch (bwrap-dev falls back
    // to one instance per step, same semantics); same gates and shape.
    let mut bj2 = bj.clone();
    bj2.procedure.invocation_mode = Some(arena_types::challenge::InvocationMode::VmPerBatch);
    let r2 = exec(&f, JobSpec::Benchmark(bj2));
    assert_pass(&r2, ObligationId::ResourceLimits);
    assert_pass(&r2, ObligationId::ProverReliability);
    let res2 = r2.benchmark.as_ref().unwrap();
    assert_eq!(res2.classes[0].runs_ns.len(), 3);
    assert!(res2.classes[0].cold_ns.is_some() && res2.classes[0].verify_median_ns > 0);
    let r = exec(&f, JobSpec::Benchmark(bj));
    assert_pass(&r, ObligationId::ResourceLimits);
    let bg = gate(&r, ObligationId::Benchmark);
    let res = r.benchmark.as_ref().unwrap();
    assert_eq!(res.classes[0].runs_ns.len(), 3);
    assert!(res.classes[0].median_ns > 0 && res.classes[0].cold_ns.is_some());
    assert!(res.classes[0].verify_median_ns > 0);
    assert_eq!(res.classes[0].proof_bytes_max, 70);
    assert!(res.measured_by.contains("DEMO-only"));
    // The fresh-confirm tripwire may legitimately fire on a noisy dev host
    // (UNKNOWN); anything else must be PASS with a score.
    assert!(
        bg.status == GateStatus::Pass || bg.summary.contains("CACHING_SUSPECTED"),
        "{}",
        bg.summary
    );
    assert!(
        res.score_milli.unwrap() > 100_000,
        "10 s baseline vs ms-scale toy prover"
    );
    assert!(r.artifact("benchmark_session").is_some());
}

#[test]
fn validate_rejects_unsafe_archive_and_wrong_challenge() {
    let f = fixture();
    // Symlink entry.
    let mut b = tar::Builder::new(Vec::new());
    let mut h = tar::Header::new_gnu();
    h.set_entry_type(tar::EntryType::Symlink);
    h.set_size(0);
    b.append_link(&mut h, "candidate.toml", "/etc/passwd")
        .unwrap();
    let pkg = f.put(&b.into_inner().unwrap());
    let v = exec(
        &f,
        JobSpec::Validate(ValidateJob {
            package: pkg,
            challenge_id: CHALLENGE.into(),
        }),
    );
    assert_fail(&v, ObligationId::PkgWellformed, ReasonCode::ArchiveUnsafe);

    let pkg = f.put(&tar_of(&package_files()));
    let v = exec(
        &f,
        JobSpec::Validate(ValidateJob {
            package: pkg,
            challenge_id: "chl_other".into(),
        }),
    );
    assert_fail(
        &v,
        ObligationId::PkgWellformed,
        ReasonCode::ChallengeUnknown,
    );

    let mut files = package_files();
    files.get_mut("build-recipe/build.sh").unwrap().0 = 0o644;
    let pkg = f.put(&tar_of(&files));
    let v = exec(
        &f,
        JobSpec::Validate(ValidateJob {
            package: pkg,
            challenge_id: CHALLENGE.into(),
        }),
    );
    assert_fail(&v, ObligationId::PkgWellformed, ReasonCode::ManifestInvalid);
}

#[test]
fn nonreproducible_and_failing_builds() {
    let f = fixture();
    let mut files = package_files();
    files.get_mut("build-recipe/build.sh").unwrap().1 =
        format!("{BUILD}\ncat /proc/sys/kernel/random/uuid > out/stamp\n").into_bytes();
    let (b, _) = f.build(&files);
    assert_fail(
        &b,
        ObligationId::BuildReproducible,
        ReasonCode::BuildNotReproducible,
    );
    assert!(gate(&b, ObligationId::BuildReproducible)
        .summary
        .contains("out/stamp"));

    let mut files = package_files();
    files.get_mut("build-recipe/build.sh").unwrap().1 =
        b"#!/bin/sh\necho compiling >&2\nexit 1\n".to_vec();
    let (b, bundle) = f.build(&files);
    assert_fail(&b, ObligationId::BuildReproducible, ReasonCode::BuildFailed);
    assert!(bundle.is_none());
    assert!(b.artifact("build_log_1").is_some());

    // Build must be offline.
    let mut files = package_files();
    files.get_mut("build-recipe/build.sh").unwrap().1 = format!(
        "{BUILD}\nif timeout 3 bash -c 'echo > /dev/tcp/1.1.1.1/53' 2>/dev/null; then exit 7; fi\n"
    )
    .into_bytes();
    let (b, _) = f.build(&files);
    assert_pass(&b, ObligationId::BuildReproducible);

    // Missing entry point output.
    let mut files = package_files();
    files.get_mut("build-recipe/build.sh").unwrap().1 =
        b"#!/bin/sh\nmkdir -p out\ncp source/prove.sh out/prove\n".to_vec();
    let (b, _) = f.build(&files);
    assert_fail(&b, ObligationId::BuildReproducible, ReasonCode::BuildFailed);
}

#[test]
fn claim_mismatch_detected() {
    let f = fixture();
    let mut files = package_files();
    // A prover that proves a *different* transition (claims over the witness).
    let cheat = PROVE.replace(r#"sha256sum < "$req""#, r#"sha256sum < "$wit""#);
    files.get_mut("source/prove.sh").unwrap().1 = cheat.into_bytes();
    let (_, bundle) = f.build(&files);
    let c = conformance(&f, &bundle.unwrap(), f.cases(2, true, claim_for));
    assert_fail(
        &c,
        ObligationId::ConformanceDifferential,
        ReasonCode::ClaimMismatch,
    );
    assert_eq!(
        gate(&c, ObligationId::ProverReliability).status,
        GateStatus::Unknown
    );
}

#[test]
fn heldout_failure_does_not_leak_case_id() {
    let f = fixture();
    let (_, bundle) = f.build(&package_files());
    let c = conformance(
        &f,
        &bundle.unwrap(),
        f.cases(1, false, |_| b"wrong".to_vec()),
    );
    assert_fail(
        &c,
        ObligationId::ConformanceDifferential,
        ReasonCode::ClaimMismatch,
    );
    for g in &c.gates {
        assert!(!g.summary.contains("heldout-secret"), "{}", g.summary);
    }
    assert!(gate(&c, ObligationId::ConformanceDifferential)
        .summary
        .contains("held-out case"));
}

#[test]
fn verifier_rejecting_honest_proof_and_prover_timeout() {
    let f = fixture();
    let mut files = package_files();
    files.get_mut("source/verify.sh").unwrap().1 = b"#!/bin/sh\nexit 1\n".to_vec();
    let (_, bundle) = f.build(&files);
    let c = conformance(&f, &bundle.unwrap(), f.cases(1, true, claim_for));
    assert_fail(
        &c,
        ObligationId::ProverReliability,
        ReasonCode::ProverFailed,
    );

    let mut files = package_files();
    files.get_mut("source/prove.sh").unwrap().1 = b"#!/bin/sh\nsleep 30\n".to_vec();
    let (_, bundle) = f.build(&files);
    let mut limits = run_limits();
    limits.max_prove_ms = 500;
    let c = exec(
        &f,
        JobSpec::Conformance(ConformanceJob {
            bundle: bundle.unwrap(),
            entry: entry(),
            params: f.put(b"p"),
            cases: f.cases(1, true, claim_for),
            limits,
            request_pin: None,
        }),
    );
    assert_fail(&c, ObligationId::ProverReliability, ReasonCode::Timeout);
}

#[test]
fn oversized_proof_is_resource_limit() {
    let f = fixture();
    let mut files = package_files();
    let fat = PROVE.replace(
        r#"> "$proof""#,
        r#"> "$proof"; head -c 10000 /dev/zero >> "$proof""#,
    );
    files.get_mut("source/prove.sh").unwrap().1 = fat.into_bytes();
    let (_, bundle) = f.build(&files);
    let c = conformance(&f, &bundle.unwrap(), f.cases(1, true, claim_for));
    assert_fail(&c, ObligationId::ResourceLimits, ReasonCode::ResourceLimit);
}

#[test]
fn lenient_verifier_fails_adversarial() {
    let f = fixture();
    let mut files = package_files();
    // Accepts anything starting with "PROOF:" — truncation/bitflips past the
    // prefix, appended garbage and swapped proofs all get through.
    let lenient = "#!/bin/sh\nwhile [ $# -gt 0 ]; do case \"$1\" in --proof) proof=$2; shift 2;; *) shift 2;; esac; done\n\
                   [ \"$(head -c 6 \"$proof\")\" = PROOF: ] && exit 0\nexit 1\n";
    files.get_mut("source/verify.sh").unwrap().1 = lenient.as_bytes().to_vec();
    let (_, bundle) = f.build(&files);
    let bundle = bundle.unwrap();
    let cases = f.cases(2, true, claim_for);
    let c = conformance(&f, &bundle, cases.clone());
    assert_pass(&c, ObligationId::ConformanceDifferential);
    let honest = cases
        .iter()
        .map(|k| HonestProof {
            case_id: k.id.clone(),
            claim: c.artifact(&format!("claim:{}", k.id)).unwrap().clone(),
            proof: c.artifact(&format!("proof:{}", k.id)).unwrap().clone(),
        })
        .collect();
    let a = exec(
        &f,
        JobSpec::Adversarial(AdversarialJob {
            bundle,
            entry: entry(),
            public_artifacts: c.artifact("public_artifacts").unwrap().clone(),
            honest,
            mutators: vec![],
            seed: 1,
            limits: run_limits(),
        }),
    );
    assert_fail(
        &a,
        ObligationId::AdversarialProofs,
        ReasonCode::HostileProofAccepted,
    );
    let s = &gate(&a, ObligationId::AdversarialProofs).summary;
    assert!(s.contains("swap") && s.contains("append"), "{s}");
}

/// Red-team RT-04: on a held-out case `prove` sees the secret witness, and
/// candidate-chosen details of its failure (output file names quoted in collect
/// errors, exit codes) used to reach the public gate summary verbatim, which is
/// a covert channel that exfiltrates held-out data.
#[test]
fn redteam_heldout_failure_details_are_not_a_covert_channel() {
    let f = fixture();
    let leak_name = PROVE.replace(
        "test -r \"$wit\"",
        "test -r \"$wit\"; ln -s /nonexistent \"$(dirname \"$claim\")/LEAK-$(cat \"$wit\")\"",
    );
    let leak_exit = PROVE.replace("test -r \"$wit\"", "test -r \"$wit\"; exit 173");
    for (what, prove) in [("file name", leak_name), ("exit code", leak_exit)] {
        let mut files = package_files();
        files.get_mut("source/prove.sh").unwrap().1 = prove.into_bytes();
        let (_, bundle) = f.build(&files);
        let bundle = bundle.unwrap();
        // control: on a PUBLIC case the details stay (useful diagnostics)
        let c = conformance(&f, &bundle, f.cases(1, true, claim_for));
        let s = &gate(&c, ObligationId::ProverReliability).summary;
        assert!(
            s.contains("witness-0") || s.contains("173"),
            "{what}: control lost detail: {s}"
        );
        // held-out: nothing candidate-chosen may reach any summary
        let c = conformance(&f, &bundle, f.cases(1, false, claim_for));
        assert_eq!(
            gate(&c, ObligationId::ProverReliability).status,
            GateStatus::Fail,
            "{what}"
        );
        for g in &c.gates {
            assert!(
                !g.summary.contains("witness-0") && !g.summary.contains("173"),
                "{what}: held-out data leaked into {:?}: {}",
                g.gate,
                g.summary
            );
        }
    }
}
