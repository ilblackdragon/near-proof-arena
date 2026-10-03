//! Stage executors end to end through bwrap-dev with the toy reference
//! candidate against the signed demo challenge. Run with `ARENA_DEV_UNSAFE=1`.

mod common;

use arena_jobs::*;
use arena_types::{GateStatus, ObligationId, ReasonCode};
use common::*;

#[test]
fn honest_candidate_passes_every_stage() {
    let f = fixture();
    let (v, _) = f.validate(&package_files());
    assert_pass(&v, ObligationId::PkgWellformed);
    assert_eq!(v.manifest.as_ref().unwrap().name, "toy-arith-reference");
    assert!(
        !gate(&v, ObligationId::PkgWellformed)
            .reason_codes
            .contains(&ReasonCode::DemoOnly),
        "validate runs no candidate code"
    );
    assert_eq!(v.execution.sandbox_backend, "bwrap-dev");
    assert_eq!(v.execution.tier_cap, arena_types::challenge::Tier::Demo);

    let (b, built) = f.build(&package_files());
    assert_pass(&b, ObligationId::BuildReproducible);
    let g = gate(&b, ObligationId::BuildReproducible);
    assert!(g.reason_codes.contains(&ReasonCode::DemoOnly));
    assert!(g.summary.starts_with("[bwrap-dev (DEMO-only)]"));
    let (pkg, manifest, out) = built.unwrap();
    assert!(out.bundle_archive.is_some() && out.public_archive.is_some());
    assert_eq!(out.certificate_decl, "");
    // every reported artifact was uploaded
    for a in &b.artifacts {
        assert!(f.store.root.join(a.digest.hex()).exists(), "{a:?}");
    }
    let job = f.exec_job(&pkg, &manifest, &out);

    let c = f.exec(JobSpec::Conformance(job.clone()));
    for g in [
        ObligationId::ConformanceDifferential,
        ObligationId::ProverReliability,
        ObligationId::ResourceLimits,
    ] {
        assert_pass(&c, g);
    }
    let s = &gate(&c, ObligationId::ConformanceDifferential).summary;
    assert!(
        s.contains("10/10 cases conform (6 public fixtures, 4 judge-sampled)"),
        "{s}"
    );
    assert!(
        !s.contains("toy-small/"),
        "sampled case ids must not leak: {s}"
    );

    let a = f.exec(JobSpec::Adversarial(job.clone()));
    assert_eq!(a.gates.len(), 1);
    let s = &gate(&a, ObligationId::AdversarialProofs).summary;
    assert_pass(&a, ObligationId::AdversarialProofs);
    assert!(s.contains(" 0 accepted") && s.contains("adv:"), "{s}");

    let r = f.exec(JobSpec::Benchmark(job));
    assert_eq!(r.gates.len(), 1, "benchmark owns only BENCHMARK");
    let bg = gate(&r, ObligationId::Benchmark);
    // The caching tripwire may legitimately fire on a noisy dev host.
    assert!(
        bg.status == GateStatus::Pass || bg.summary.contains("CACHING_SUSPECTED"),
        "{}",
        bg.summary
    );
    if bg.status == GateStatus::Pass {
        let res = r.benchmark.as_ref().unwrap();
        assert_eq!(res.classes.len(), 2);
        assert_eq!(res.suite_revision, f.chal.workload_suite.revision);
        assert_eq!(
            res.classes[0].runs_ns.len(),
            f.chal.measurement.measured_runs as usize
        );
        assert!(
            res.score_milli.is_none(),
            "demo challenge has no baselines: unscored"
        );
        assert!(
            res.measured_by.contains("batch sizes capped") && res.measured_by.contains("DEMO-only")
        );
        assert!(res
            .classes
            .iter()
            .all(|c| c.proof_bytes_max == 40 && c.cold_ns.is_some()));
    }
}

#[test]
fn validate_rejections() {
    let f = fixture();
    // Symlink entry.
    let mut b = tar::Builder::new(Vec::new());
    let mut h = tar::Header::new_gnu();
    h.set_entry_type(tar::EntryType::Symlink);
    h.set_size(0);
    b.append_link(&mut h, "candidate.toml", "/etc/passwd")
        .unwrap();
    let pkg = f.put(&b.into_inner().unwrap());
    let v = f.exec(JobSpec::Validate(ValidateJob {
        ctx: f.ctx(&pkg),
        challenge: f.chal.clone(),
    }));
    assert_fail(&v, ObligationId::PkgWellformed, ReasonCode::ArchiveUnsafe);

    let mut files = package_files();
    let m = String::from_utf8(files["candidate.toml"].1.clone())
        .unwrap()
        .replace(CHALLENGE, "chl_ffffffffffffffffffffffffffffffff");
    set(&mut files, "candidate.toml", &m);
    assert_fail(
        &f.validate(&files).0,
        ObligationId::PkgWellformed,
        ReasonCode::ChallengeUnknown,
    );

    let mut files = package_files();
    let m = String::from_utf8(files["candidate.toml"].1.clone())
        .unwrap()
        .replace("validity-classical-128", "zk-classical-128");
    set(&mut files, "candidate.toml", &m);
    assert_fail(
        &f.validate(&files).0,
        ObligationId::PkgWellformed,
        ReasonCode::ProfileNotAllowed,
    );

    let mut files = package_files();
    files.get_mut("build-recipe/build.sh").unwrap().0 = 0o644;
    assert_fail(
        &f.validate(&files).0,
        ObligationId::PkgWellformed,
        ReasonCode::ManifestInvalid,
    );
}

#[test]
fn build_failures() {
    let f = fixture();
    let mut files = package_files();
    set(&mut files, "build-recipe/build.sh", "#!/bin/sh\nset -e\nsh build-recipe/real.sh\ncat /proc/sys/kernel/random/uuid > out/stamp\n");
    files.insert(
        "build-recipe/real.sh".into(),
        package_files()["build-recipe/build.sh"].clone(),
    );
    let m = String::from_utf8(files["candidate.toml"].1.clone())
        .unwrap()
        .replace("\"out/verify\"]", "\"out/verify\", \"out/stamp\"]");
    set(&mut files, "candidate.toml", &m);
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
    set(
        &mut files,
        "build-recipe/build.sh",
        "#!/bin/sh\necho compiling >&2\nexit 1\n",
    );
    let (b, built) = f.build(&files);
    assert_fail(&b, ObligationId::BuildReproducible, ReasonCode::BuildFailed);
    assert!(built.is_none());

    // Offline: a build that needs the network fails.
    let mut files = package_files();
    set(
        &mut files,
        "build-recipe/build.sh",
        "#!/bin/sh\nset -e\nexec 3<>/dev/tcp/1.1.1.1/80\n",
    );
    let (b, _) = f.build(&files);
    assert_fail(&b, ObligationId::BuildReproducible, ReasonCode::BuildFailed);

    // Nondeterministic prepare.
    let mut files = package_files();
    let p = String::from_utf8(files["source/prepare.c"].1.clone())
        .unwrap()
        .replace("const char *key = \"toy-arith-checksum-key-v1\";", "char key[64]; FILE *u = fopen(\"/proc/sys/kernel/random/uuid\", \"r\"); if (!u || !fgets(key, sizeof key, u)) return 2;");
    set(&mut files, "source/prepare.c", &p);
    let (b, _) = f.build(&files);
    assert_fail(
        &b,
        ObligationId::BuildReproducible,
        ReasonCode::BuildNotReproducible,
    );
    assert!(gate(&b, ObligationId::BuildReproducible)
        .summary
        .contains("prepare is nondeterministic"));
}

fn built(f: &Fixture, files: &std::collections::BTreeMap<String, (u32, Vec<u8>)>) -> ExecJob {
    let (b, built) = f.build(files);
    let (pkg, manifest, out) = built.unwrap_or_else(|| panic!("build failed: {:?}", b.gates));
    f.exec_job(&pkg, &manifest, &out)
}

#[test]
fn claim_mismatch_detected() {
    let f = fixture();
    let mut files = package_files();
    // Proves a different statement: c = a + b.
    let p = String::from_utf8(files["source/prove.c"].1.clone())
        .unwrap()
        .replace("le64(r) * le64(r + 8)", "le64(r) + le64(r + 8)");
    let v = String::from_utf8(files["source/verify.c"].1.clone())
        .unwrap()
        .replace(
            "le64(claim) * le64(claim + 8)",
            "le64(claim) + le64(claim + 8)",
        );
    set(&mut files, "source/prove.c", &p);
    set(&mut files, "source/verify.c", &v);
    let c = f.exec(JobSpec::Conformance(built(&f, &files)));
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
fn verifier_rejecting_honest_proof_and_prover_timeout() {
    let f = fixture();
    let mut files = package_files();
    set(
        &mut files,
        "source/verify.c",
        "int main(void) { return 1; }\n",
    );
    let job = built(&f, &files);
    let c = f.exec(JobSpec::Conformance(job.clone()));
    assert_fail(
        &c,
        ObligationId::ProverReliability,
        ReasonCode::ProverFailed,
    );
    let a = f.exec(JobSpec::Adversarial(job));
    assert_eq!(
        gate(&a, ObligationId::AdversarialProofs).status,
        GateStatus::Unknown,
        "vacuous: never PASS"
    );

    let mut files = package_files();
    set(
        &mut files,
        "source/prove.c",
        "#include <unistd.h>\nint main(void) { for (;;) pause(); }\n",
    );
    let mut job = built(&f, &files);
    job.challenge.resource_limits.max_prove_ms = 500;
    let c = f.exec(JobSpec::Conformance(job));
    assert_fail(&c, ObligationId::ProverReliability, ReasonCode::Timeout);
}

#[test]
fn oversized_proof_is_resource_limit() {
    let f = fixture();
    let mut files = package_files();
    let p = String::from_utf8(files["source/prove.c"].1.clone()).unwrap().replace(
        "return (write_file(co, claim, 24) || write_file(po, proof, PROOF_LEN)) ? 2 : 0;",
        "static unsigned char big[2 << 20]; memcpy(big, proof, PROOF_LEN); return (write_file(co, claim, 24) || write_file(po, big, sizeof big)) ? 2 : 0;",
    );
    set(&mut files, "source/prove.c", &p);
    let c = f.exec(JobSpec::Conformance(built(&f, &files)));
    assert_fail(&c, ObligationId::ResourceLimits, ReasonCode::ResourceLimit);
}

#[test]
fn lenient_verifier_fails_adversarial() {
    let f = fixture();
    let mut files = package_files();
    // Accepts any proof that starts with the magic.
    set(
        &mut files,
        "source/verify.c",
        "#include \"common.h\"\n#include <string.h>\nint main(int c, char **v) { unsigned char p[1 << 16]; long n = read_file(arg(c, v, \"--proof\"), p, sizeof p); return (n >= 8 && !memcmp(p, PROOF_MAGIC, 8)) ? 0 : 1; }\n",
    );
    let job = built(&f, &files);
    let c = f.exec(JobSpec::Conformance(job.clone()));
    assert_pass(&c, ObligationId::ConformanceDifferential);
    let a = f.exec(JobSpec::Adversarial(job));
    assert_fail(
        &a,
        ObligationId::AdversarialProofs,
        ReasonCode::HostileProofAccepted,
    );
    let s = &gate(&a, ObligationId::AdversarialProofs).summary;
    assert!(s.contains("swap") && s.contains("append"), "{s}");
}

#[test]
fn benchmark_failure_is_benchmark_gate() {
    let f = fixture();
    let mut files = package_files();
    // Correct on the public fixtures (a, b < 2^16), wrong on sampled inputs.
    let p = String::from_utf8(files["source/prove.c"].1.clone())
        .unwrap()
        .replace(
            "le64(r) * le64(r + 8)",
            "(le64(r) < 65536 && le64(r + 8) < 65536 ? le64(r) * le64(r + 8) : 0)",
        );
    set(&mut files, "source/prove.c", &p);
    let job = built(&f, &files);
    let r = f.exec(JobSpec::Benchmark(job));
    assert_eq!(r.gates.len(), 1);
    assert_fail(&r, ObligationId::Benchmark, ReasonCode::ClaimMismatch);
    assert!(r.benchmark.is_none());
}

#[test]
fn fork_bomb_and_background_daemon() {
    let f = fixture();
    // Honest outputs, then a fork bomb left behind: RESOURCE_LIMITS.
    let mut files = package_files();
    let p = String::from_utf8(files["source/prove.c"].1.clone()).unwrap().replace(
        "return (write_file(co, claim, 24) || write_file(po, proof, PROOF_LEN)) ? 2 : 0;",
        "if (write_file(co, claim, 24) || write_file(po, proof, PROOF_LEN)) return 2; for (;;) if (fork() < 0) break; return 0;",
    );
    set(
        &mut files,
        "source/prove.c",
        &format!("#include <unistd.h>\n{p}"),
    );
    let c = f.exec(JobSpec::Conformance(built(&f, &files)));
    assert_fail(&c, ObligationId::ResourceLimits, ReasonCode::ResourceLimit);

    // The proof is "finished later" by a daemon: it never reaches the judge.
    let mut files = package_files();
    let p = String::from_utf8(files["source/prove.c"].1.clone()).unwrap().replace(
        "return (write_file(co, claim, 24) || write_file(po, proof, PROOF_LEN)) ? 2 : 0;",
        "if (write_file(co, claim, 24)) return 2; if (fork() == 0) { sleep(2); write_file(po, proof, PROOF_LEN); _exit(0); } return 0;",
    );
    set(
        &mut files,
        "source/prove.c",
        &format!("#include <unistd.h>\n{p}"),
    );
    let c = f.exec(JobSpec::Conformance(built(&f, &files)));
    assert_fail(
        &c,
        ObligationId::ProverReliability,
        ReasonCode::ProverFailed,
    );
}

/// Red-team RT-04 (ported to the oracle-driven worker): on a non-public case
/// `prove` sees inputs the submitter must not learn, and candidate-chosen
/// failure details (output names quoted by the collector, exit codes) must
/// not reach any gate summary; on public fixtures the details stay.
#[test]
fn redteam_heldout_failure_details_are_not_a_covert_channel() {
    let mut f = fixture();
    let base = String::from_utf8(package_files()["source/prove.c"].1.clone()).unwrap();
    let marker = "  memcpy(claim, r, 16);";
    let leak_name = base.replace(
        marker,
        &format!("  {{ char n[4200]; snprintf(n, sizeof n, \"%s.LEAK-%02x%02x%02x%02x\", co, r[0], r[1], r[2], r[3]); if (symlink(\"/nonexistent\", n)) return 2; }}\n{marker}"),
    );
    let leak_exit = base.replace(
        marker,
        &format!("  if (r[0] != 0xff) return 173;\n{marker}"),
    );
    for (what, prove) in [("file name", leak_name), ("exit code", leak_exit)] {
        let mut files = package_files();
        set(
            &mut files,
            "source/prove.c",
            &format!("#include <unistd.h>\n{prove}"),
        );
        let job = built(&f, &files);
        // control: public fixtures keep their details
        let c = f.exec(JobSpec::Conformance(job.clone()));
        let s = &gate(&c, ObligationId::ProverReliability).summary;
        assert!(
            s.contains("LEAK-") || s.contains("173"),
            "{what}: control lost detail: {s}"
        );
        // only judge-sampled (non-public) cases
        let saved = std::mem::replace(
            &mut f.exec.ctx.oracles,
            arena_worker::oracle::Oracles::builtin(),
        );
        let c = f.exec(JobSpec::Conformance(job));
        f.exec.ctx.oracles = saved;
        assert_eq!(
            gate(&c, ObligationId::ProverReliability).status,
            GateStatus::Fail,
            "{what}"
        );
        for g in &c.gates {
            assert!(
                !g.summary.contains("LEAK-") && !g.summary.contains("173"),
                "{what}: leaked into {:?}: {}",
                g.gate,
                g.summary
            );
        }
    }
}
