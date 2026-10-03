//! `verify_route = "npai-v1"` and `"native-lean"` verification paths: every
//! verify call runs a JUDGE-owned verifier (npai-verify on the judge-built
//! bytecode, bound to the certified digest; or the judge-built native
//! binary), never the candidate's `out/verify`; npai results are shadowed
//! on the Lean reference interpreter.

mod common;

use arena_jobs::*;
use arena_types::{challenge::FormalParams, ChallengeDefinition, GateStatus, ObligationId, ReasonCode};
use arena_worker::executor::JobExecutor;
use common::*;
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;

fn bin(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_BIN_EXE_arena-worker")).parent().unwrap().to_path_buf();
    let p = dir.join(name);
    if !p.is_file() {
        let st = std::process::Command::new(env!("CARGO"))
            .args(["build", "-q", "-p", "arena-npai", "--bin", name])
            .current_dir(repo())
            .status()
            .unwrap();
        assert!(st.success());
    }
    p
}

fn interp_ref() -> Option<PathBuf> {
    let p = repo().join("formal-core/.lake/build/bin/arena-interp-ref");
    p.is_file().then_some(p)
}

/// The toy candidate on the npai-v1 route. Its own `verify` accepts
/// EVERYTHING: if the judge ever ran it, adversarial would fail.
fn npai_package() -> std::collections::BTreeMap<String, (u32, Vec<u8>)> {
    let mut files = package_files();
    let data = repo().join("runners/worker/tests/data");
    let image = arena_npai::asm::assemble_image(&std::fs::read_to_string(data.join("toy-npai.s")).unwrap()).unwrap();
    files.insert("source/verifier.npai".into(), (0o644, image));
    files.insert("source/sha256.c".into(), (0o644, std::fs::read(data.join("sha256.c")).unwrap()));
    files.insert("source/prove.c".into(), (0o644, std::fs::read(data.join("prove-npai.c")).unwrap()));
    set(&mut files, "source/verify.c", "int main(void) { return 0; }\n");
    let p = String::from_utf8(files["source/prepare.c"].1.clone()).unwrap().replace("\"%s/key\"", "\"%s/public.bin\"");
    set(&mut files, "source/prepare.c", &p);
    set(
        &mut files,
        "build-recipe/build.sh",
        "#!/bin/sh\nset -eu\nmkdir -p out\ncc -O2 -std=c99 -o out/prepare source/common.c source/prepare.c\ncc -O2 -std=c99 -o out/prove source/common.c source/sha256.c source/prove.c\ncc -O2 -std=c99 -o out/verify source/verify.c\ncp source/verifier.npai out/verifier.npai\n",
    );
    let m = String::from_utf8(files["candidate.toml"].1.clone())
        .unwrap()
        .replace("\"out/verify\"]", "\"out/verify\", \"out/verifier.npai\"]")
        .replace("verify = \"out/verify\"\n", "verify = \"out/verify\"\nverify_route = \"npai-v1\"\nverifier_bytecode = \"out/verifier.npai\"\n");
    set(&mut files, "candidate.toml", &m);
    files
}

fn with_fuel(mut c: ChallengeDefinition) -> ChallengeDefinition {
    c.formal_params = Some(FormalParams { verify_fuel: 100_000, max_proof_bytes: c.resource_limits.max_proof_bytes, max_reduction_fuel: 1 << 20 });
    c
}

fn npai_job(f: &mut Fixture) -> ExecJob {
    f.chal = with_fuel(f.chal.clone());
    f.exec.ctx.npai_verify = Some(bin("npai-verify"));
    let (b, built) = f.build(&npai_package());
    let (pkg, manifest, out) = built.unwrap_or_else(|| panic!("{:?}", b.gates));
    assert_eq!(out.verify, arena_types::Digest::of_bytes(&arena_npai::asm::assemble_image(&std::fs::read_to_string(repo().join("runners/worker/tests/data/toy-npai.s")).unwrap()).unwrap()), "verify artifact = bytecode");
    f.exec_job(&pkg, &manifest, &out)
}

#[test]
fn npai_route_runs_the_judges_interpreter() {
    let mut f = fixture();
    f.exec.ctx.interp_ref = interp_ref();
    let job = npai_job(&mut f);
    let c = f.exec(JobSpec::Conformance(job.clone()));
    for g in [ObligationId::ConformanceDifferential, ObligationId::ProverReliability, ObligationId::ResourceLimits] {
        assert_pass(&c, g);
    }
    if f.exec.ctx.interp_ref.is_some() {
        let s = &gate(&c, ObligationId::ConformanceDifferential).summary;
        assert!(s.contains("npai shadow (Lean reference)") && !s.contains(": 0 agreed"), "{s}");
    }
    // The candidate's always-accept `verify` is never run: hostile proofs are
    // rejected by the judge's interpreter.
    let a = f.exec(JobSpec::Adversarial(job.clone()));
    assert_pass(&a, ObligationId::AdversarialProofs);
    assert!(gate(&a, ObligationId::AdversarialProofs).summary.contains(" 0 accepted"));
    let r = f.exec(JobSpec::Benchmark(job));
    assert_pass(&r, ObligationId::Benchmark);
}

#[test]
fn npai_route_without_judge_interpreter_or_fuel_is_unknown() {
    let mut f = fixture();
    let job = npai_job(&mut f);
    f.exec.ctx.npai_verify = None;
    let c = f.exec(JobSpec::Conformance(job.clone()));
    assert_eq!(gate(&c, ObligationId::ConformanceDifferential).status, GateStatus::Unknown);
    f.exec.ctx.npai_verify = Some(bin("npai-verify"));
    let mut job = job;
    job.challenge.formal_params = None;
    let a = f.exec(JobSpec::Adversarial(job));
    assert_eq!(gate(&a, ObligationId::AdversarialProofs).status, GateStatus::Unknown);
}

#[test]
fn npai_shadow_disagreement_is_an_infra_alert() {
    let mut f = fixture();
    // A "reference" that always claims acceptance with a bogus fuel count.
    let fake = f.tmp.path().join("fake-ref");
    std::fs::write(&fake, "#!/bin/sh\necho '{\"outcome\":\"accept\",\"fuel_used\":1}'\nexit 0\n").unwrap();
    std::fs::set_permissions(&fake, std::os::unix::fs::PermissionsExt::from_mode(0o755)).unwrap();
    f.exec.ctx.interp_ref = Some(fake);
    let job = npai_job(&mut f);
    let e = f.exec.execute(&JobSpec::Adversarial(job), "a", &AtomicBool::new(false)).unwrap_err();
    assert!(e.to_string().contains("ALERT: npai interpreter disagreement"), "{e}");
}

#[test]
fn native_lean_route_runs_the_judge_built_binary() {
    let f = fixture();
    // Candidate with an always-accept `verify` on the native-lean route.
    let mut files = package_files();
    set(&mut files, "source/verify.c", "int main(void) { return 0; }\n");
    let m = String::from_utf8(files["candidate.toml"].1.clone())
        .unwrap()
        .replace("verify = \"out/verify\"\n", "verify = \"out/verify\"\nverify_route = \"native-lean\"\n")
        + "\n[formal]\nlean_project = \"formal\"\ncertificate = \"Candidate.certificate\"\nverifier_model = \"Candidate.Model.verify\"\nverifier_model_module = \"Candidate.Model\"\n";
    set(&mut files, "candidate.toml", &m);
    files.insert("formal/Candidate.lean".into(), (0o644, b"-- placeholder\n".to_vec()));
    let (b, built) = f.build(&files);
    let (pkg, manifest, mut out) = built.unwrap_or_else(|| panic!("{:?}", b.gates));
    let job = f.exec_job(&pkg, &manifest, &out);
    // Without a judge-built verifier recorded by FORMAL_CHECK: UNKNOWN.
    let c = f.exec(JobSpec::Conformance(job));
    assert_eq!(gate(&c, ObligationId::ConformanceDifferential).status, GateStatus::Unknown);
    // A "judge-built" verifier that rejects everything: the candidate's
    // accept-all binary is not what runs.
    out.native_verifier = Some(f.put(b"#!/bin/sh\nexit 1\n"));
    let c = f.exec(JobSpec::Conformance(f.exec_job(&pkg, &manifest, &out)));
    assert_fail(&c, ObligationId::ProverReliability, ReasonCode::ProverFailed);
    assert!(gate(&c, ObligationId::ProverReliability).summary.contains("verify rejected the honest proof"));
}

#[test]
fn npai_exit3_is_binding_failure_never_reject() {
    use arena_sandbox::ExitStatus;
    use arena_worker::stages::common::{verdict_for, Verdict, Verifier};
    let npai = Verifier::Npai { tool: "x".into(), image: "y".into(), fuel: 1, digest_hex: String::new(), shadow: None };
    assert_eq!(verdict_for(&npai, ExitStatus::Exited(3)), Verdict::BindingMismatch);
    assert_eq!(verdict_for(&npai, ExitStatus::Exited(1)), Verdict::Reject);
    assert_eq!(verdict_for(&npai, ExitStatus::Exited(2)), Verdict::Error);
    assert_eq!(verdict_for(&Verifier::Candidate, ExitStatus::Exited(3)), Verdict::Error);
}

/// The npai route in Firecracker microVMs, with a static (musl) judge
/// `npai-verify` mounted read-only. Gated: `ARENA_FC_TESTS=1`.
#[test]
fn npai_route_in_firecracker() {
    if std::env::var("ARENA_FC_TESTS").as_deref() != Ok("1") {
        eprintln!("skipped: set ARENA_FC_TESTS=1");
        return;
    }
    let target = repo().join("target/static");
    let st = std::process::Command::new(env!("CARGO"))
        .args(["build", "-q", "--release", "--target", "x86_64-unknown-linux-musl", "-p", "arena-npai", "--bin", "npai-verify"])
        .env("CARGO_TARGET_DIR", &target)
        .env("RUSTFLAGS", "-C target-feature=+crt-static")
        .current_dir(repo())
        .status()
        .unwrap();
    assert!(st.success());
    let tool = target.join("x86_64-unknown-linux-musl/release/npai-verify");
    let mut f = fixture();
    let job = npai_job(&mut f);
    let deps = std::env::var_os("ARENA_FC_DEPS").map(PathBuf::from).unwrap_or_else(|| "/data/illia/nearproof-deps/firecracker".into());
    let cfg = arena_firecracker::FirecrackerConfig::from_deps_dir(&deps, &deps.join("work-worker-tests")).unwrap();
    let fc = arena_firecracker::FirecrackerSandbox::new(cfg).unwrap();
    let mut exec = common::executor(std::sync::Arc::new(fc), f.store.clone(), &f.tmp.path().join("fc-npai"));
    exec.ctx.npai_verify = Some(tool);
    for spec in [JobSpec::Conformance(job.clone()), JobSpec::Adversarial(job)] {
        let r = exec.execute(&spec, "fc-npai", &AtomicBool::new(false)).unwrap();
        for g in &r.gates {
            assert_eq!(g.status, GateStatus::Pass, "{:?}: {} // {:?}", g.gate, g.summary, r.gates.iter().map(|g| (&g.gate, &g.summary)).collect::<Vec<_>>());
        }
    }
}
