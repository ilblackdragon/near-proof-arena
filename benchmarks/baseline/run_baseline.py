#!/usr/bin/env python3
"""Measure a challenge baseline (reference candidate) per bench-spec-v1.

Pipeline (every step recorded in OUT_DIR):

  1. pack the reference package with `arena pack` (package digest = sha256 of
     the deterministic archive) and build it offline in a fresh HOME with its
     own build-recipe; record the entry-point digests;
  2. collect the host profile (`arena_bench host-profile`) — on the shared dev
     host this is NOT a governed host, and every number is labelled dev-host;
  3. check every generator spec's JCS digest against the challenge's
     `workload_suite.classes[].generator`; the worker's NEAR oracle samples the
     batches itself with public seeds derive_seed("workload", class,
     challenge_id, package_digest) (`<class>#fresh` for fresh-confirm), so
     anyone can regenerate the inputs;
  4. run the judge-equivalent `prepare` on the approved params to freeze the
     public dir;
  5. run the session through the worker's real BENCHMARK stage on Firecracker
     (`cargo run -p arena-worker --example bench_session`), with calibration
     pre/post;
  6. summarise: per-class medians/MAD/cold/verify, outliers, tripwire,
     calibration drift (`arena_bench.calibration.check_drift`), load average,
     and the cost_v1 components (per-run verify and proof-byte totals and
     their medians, BENCHMARK_SPEC §14.3);
  7. with `--control-sessions N`: N more sessions of the same bundle on the
     same CPUs and the same sampled batches, each checked against the first
     by the verify drift control (`arena_bench.cost.verify_control`,
     BENCHMARK_SPEC §14.4, 30 000 ppm). `summary.json` records the verdicts;
     `pin_baseline.py` refuses a cost baseline whose control failed.

`--package-rev REV` packs the package as committed at REV (default HEAD), e.g.
to re-measure a challenge's pinned `baseline_submission`; the summary records
whether the packed digest equals it.

usage: run_baseline.py --challenge challenges/chl_….json --package examples/reexec-witness
                       --oracle oracle/target/debug/near-arena-oracle --out benchmarks/results/<name>
"""
import argparse, datetime, hashlib, json, os, shutil, subprocess, sys, tempfile

REPO = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True).stdout.strip()
sys.path.insert(0, os.path.join(REPO, "benchmarks"))
from arena_bench import calibration, cost, hostprofile, stats  # noqa: E402


def jcs(v):
    return json.dumps(v, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def sha256_file(p):
    return "sha256:" + hashlib.sha256(open(p, "rb").read()).hexdigest()


def run(cmd, **kw):
    print("+", " ".join(cmd), file=sys.stderr)
    return subprocess.run(cmd, check=True, **kw)


CROSS_SESSION_CALIBRATION_PPM = 20_000  # §6.1 session-drift threshold, applied between sessions


def control_verdicts(classes, controls, stat="median", pinned_cal=None):
    """§14.4 verify drift control of each control session against the first.

    A control is valid only if its own calibration passed (§6.1) and its
    calibration median (pre ∪ post) is within 20 000 ppm of the pinned
    session's: a control taken in another host state measures the host, not
    the reference."""
    pinned = {c["class_id"]: c.get("verify_stat_ns", c.get("verify_run_median_ns")) for c in classes}
    out = []
    for path, cs in controls:
        runs = {c["class_id"]: c["measured_verify_runs_ns"] for c in cs["session"]["classes"]}
        v = cost.verify_control(pinned, runs, stat=stat)
        cal = calibration.check_drift(cs["calibration"]["pre_ns"], cs["calibration"]["post_ns"])
        ctl_cal = stats.median_u64(cs["calibration"]["pre_ns"] + cs["calibration"]["post_ns"])
        xcal = calibration.drift_ppm(pinned_cal, ctl_cal) if pinned_cal else None
        out.append({
            "session": os.path.basename(path),
            "ok": v.ok,
            "reasons": list(v.reasons),
            "tolerance_ppm": v.tolerance_ppm,
            "classes": [c.__dict__ for c in v.classes],
            "prove_median_ns": {c["class_id"]: stats.median_u64(c["measured_runs_ns"]) for c in cs["session"]["classes"]},
            "proof_bytes_run_median": {c["class_id"]: stats.median_u64(c["measured_proof_bytes_runs"])
                                       for c in cs["session"]["classes"]},
            "flags": cs["session"]["flags"],
            "calibration_ok": cal.ok,
            "calibration_reasons": list(cal.reasons),
            "session_wall_secs": cs["session_wall_secs"],
            # §6.1: a session whose calibration failed (or that is flagged) is
            # infra-invalid; its control verdict does not count either way
            "calibration_median_ns": ctl_cal,
            "calibration_vs_pinned_ppm": xcal,
            "valid": cal.ok and not cs["session"]["flags"]
                     and (xcal is None or xcal <= CROSS_SESSION_CALIBRATION_PPM),
        })
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--challenge", required=True)
    ap.add_argument("--package", required=True, help="reference candidate package dir (tracked files only are packed)")
    ap.add_argument("--oracle", default=None, help="near-arena-oracle (v1/v2 claim encodings)")
    ap.add_argument("--oracle-v3", default=None, help="near-arena-oracle-v3 (near-arena-claim-v3, D0 generator specs)")
    ap.add_argument("--oracle-v3-d1", default=None, help="near-arena-oracle-v3-d1 (near-arena-claim-v3, D1/D2 specs)")
    ap.add_argument("--oracle-v3-d3", default=None, help="near-arena-oracle-v3-d3 (near-arena-claim-v3, D3 specs)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--cpus", default="8-15")
    ap.add_argument("--host-id", default="dev-illia-32c")
    ap.add_argument("--work", default=None, help="scratch dir (default: a temp dir)")
    ap.add_argument("--calibration-runs", default="5")
    ap.add_argument("--fixtures", default=os.path.join(REPO, "oracle/fixtures/public"),
                    help="public fixtures dir (TreeDigest must equal workload_suite.public_fixtures)")
    ap.add_argument("--fc-deps", default=None, help="Firecracker deps dir (images built from this checkout)")
    ap.add_argument("--workloads", default=os.path.join(REPO, "spec/workloads/near-transfer-receipt-v1"),
                    help="generator spec dir(s), comma-separated, with <class>.json (digests must match the "
                         "challenge; near-chunk-v3: spec/workloads/near-chunk-validation-d0,spec/workloads/near-chunk-v3)")
    ap.add_argument("--season-secret-file", default=None,
                    help="judge-only season secret (hex, 0600): sample batches as a live worker with "
                         "ARENA_SEASON_SECRET_FILE does (BENCHMARK_SPEC §11.1); never printed")
    ap.add_argument("--season-secret-commit", default=None, help="published commitment the secret must match")
    ap.add_argument("--package-rev", default="HEAD", help="pack the package as committed at this git revision")
    ap.add_argument("--control-sessions", type=int, default=0,
                    help="extra sessions of the same bundle for the verify drift control (BENCHMARK_SPEC §14.4)")
    ap.add_argument("--verify-statistic", default="median", choices=list(cost.VERIFY_STATISTICS),
                    help="aggregation of per-run verify totals for cost_baseline and the control (§14.3)")
    ap.add_argument("--before-session", default=None,
                    help="shell command run once after the build, right before the first session "
                         "(e.g. stop the live benchmark worker: keeps the CPU window to the sessions)")
    a = ap.parse_args()
    if not (a.oracle or a.oracle_v3 or a.oracle_v3_d1 or a.oracle_v3_d3):
        sys.exit("give --oracle and/or --oracle-v3 [--oracle-v3-d1 --oracle-v3-d3]")
    workload_dirs = [os.path.abspath(w) for w in a.workloads.split(",") if w]

    chal_path = os.path.abspath(a.challenge)
    chal = json.load(open(chal_path))
    chal_id = "chl_" + hashlib.sha256(jcs(chal).encode()).hexdigest()[:32]
    out = os.path.abspath(a.out)
    os.makedirs(out, exist_ok=True)
    work = os.path.abspath(a.work) if a.work else tempfile.mkdtemp(prefix="arena-baseline-")
    os.makedirs(work, exist_ok=True)
    arena = os.path.join(REPO, "target/debug/arena")

    # 1. pack (from a clean export of the tracked files) + build
    export = os.path.join(work, "export")
    shutil.rmtree(export, ignore_errors=True)
    os.makedirs(export)
    rel = os.path.relpath(os.path.abspath(a.package), REPO)
    rev = subprocess.run(["git", "-C", REPO, "rev-parse", a.package_rev], capture_output=True, text=True, check=True).stdout.strip()
    git_tree = subprocess.run(["git", "-C", REPO, "rev-parse", f"{rev}:{rel}"], capture_output=True, text=True, check=True).stdout.strip()
    archive = subprocess.run(["git", "-C", REPO, "archive", rev, rel], capture_output=True, check=True).stdout
    subprocess.run(["tar", "-x", "-C", export], input=archive, check=True)
    pkg_dir = os.path.join(export, rel)
    pkg_tar = os.path.join(work, "package.tar")
    run([arena, "pack", "-o", pkg_tar, pkg_dir], stdout=subprocess.DEVNULL)
    package_digest = sha256_file(pkg_tar)
    build = os.path.join(work, "build")
    shutil.rmtree(build, ignore_errors=True)
    os.makedirs(build)
    run(["tar", "-xf", pkg_tar, "-C", build])
    home = os.path.join(work, "home")
    shutil.rmtree(home, ignore_errors=True)
    os.makedirs(home)
    env = dict(os.environ, HOME=home, SOURCE_DATE_EPOCH="0",
               RUSTUP_HOME=os.environ.get("RUSTUP_HOME", os.path.expanduser("~/.rustup")),
               ELAN_HOME=os.environ.get("ELAN_HOME", os.path.expanduser("~/.elan")))
    with open(os.path.join(out, "build.log"), "w") as log:
        run(["bash", "build-recipe/build.sh"], cwd=build, env=env, stdout=log, stderr=subprocess.STDOUT)
    entry = {n: sha256_file(os.path.join(build, "out", n)) for n in ("prepare", "prove", "verify")}
    # the bundle handed to the worker: the package plus the built entry points
    bundle = os.path.join(work, "bundle")
    shutil.rmtree(bundle, ignore_errors=True)
    os.makedirs(bundle)
    run(["tar", "-xf", pkg_tar, "-C", bundle])
    shutil.copytree(os.path.join(build, "out"), os.path.join(bundle, "out"))

    # 2. host profile
    note = (f"shared development host, NOT governed hardware; benchmark cpus {a.cpus} (no isolcpus, SMT on, "
            "other tenants' load present). Numbers are dev-host measurements, never official.")
    hp = hostprofile.collect(a.host_id, governed=False, note=note)
    json.dump(hp, open(os.path.join(out, "host-profile.json"), "w"), indent=1)

    # 3. generator specs (the worker's oracle samples with them)
    gens = {}
    for c in chal["workload_suite"]["classes"]:
        cand = [os.path.join(w, c["id"] + ".json") for w in workload_dirs]
        spec_p = next((p for p in cand if os.path.exists(p)), cand[0])
        spec = json.load(open(spec_p))
        d = "sha256:" + hashlib.sha256(jcs(spec).encode()).hexdigest()
        if d != c["generator"]:
            sys.exit(f"generator spec {spec_p} digest {d} != challenge generator {c['generator']}")
        gens[c["id"]] = {"spec": os.path.relpath(spec_p, REPO), "digest": d}
    oracle_commit = open(os.path.join(REPO, "oracle/NEARCORE_PIN")).read()

    # 4. frozen public dir: the reference's prepare on the approved params
    fixtures = os.path.abspath(a.fixtures)
    public = os.path.join(work, "public")
    shutil.rmtree(public, ignore_errors=True)
    run([os.path.join(bundle, "out/prepare"), "--params", os.path.join(fixtures, "params.bin"), "--out", public])

    # 5. the session (+ control sessions)
    session_json = os.path.join(out, "session.json")
    run_chal = chal_path
    hw_label = f"dev-host:{a.host_id} (NOT {chal['hardware_profile']['id']} governed)"
    argv = ["cargo", "run", "-q", "-j", "8", "-p", "arena-worker", "--example", "bench_session", "--",
            "--challenge", run_chal, "--package", pkg_tar, "--bundle-dir", bundle, "--public-dir", public,
            "--native-verifier", os.path.join(bundle, "out/verify"),
            *(["--oracle", os.path.abspath(a.oracle)] if a.oracle else []),
            *(["--oracle-v3", os.path.abspath(a.oracle_v3)] if a.oracle_v3 else []),
            *(["--oracle-v3-d1", os.path.abspath(a.oracle_v3_d1)] if a.oracle_v3_d1 else []),
            *(["--oracle-v3-d3", os.path.abspath(a.oracle_v3_d3)] if a.oracle_v3_d3 else []),
            "--generators", ",".join(workload_dirs),
            "--fixtures", fixtures, "--cpus", a.cpus, "--calibration-runs", a.calibration_runs,
            "--work", os.path.join(work, "session"), "--out", "SESSION_OUT"]
    if a.fc_deps:
        argv += ["--fc-deps", os.path.abspath(a.fc_deps)]
    if a.season_secret_file:
        argv += ["--season-secret-file", os.path.abspath(a.season_secret_file)]
        if a.season_secret_commit:
            argv += ["--season-secret-commit", a.season_secret_commit]
    def session(path):
        shutil.rmtree(os.path.join(work, "session"), ignore_errors=True)
        argv_i = [path if x == "SESSION_OUT" else x for x in argv]
        run(argv_i, cwd=REPO, env=dict(os.environ, RUSTC_WRAPPER=os.environ.get("RUSTC_WRAPPER", "sccache")))
        return json.load(open(path))

    if a.before_session:
        run(["sh", "-c", a.before_session])
    started = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
    s = session(session_json)
    controls = [(os.path.join(out, f"session-control-{i + 1}.json"),) for i in range(a.control_sessions)]
    controls = [(p, session(p)) for (p,) in controls]
    finished = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")

    # 6. summary
    gates = {g["gate"]: g for g in s["job_result"]["gates"]}
    cal = s["calibration"]
    dv = calibration.check_drift(cal["pre_ns"], cal["post_ns"])
    classes = []
    for cs in s["session"]["classes"]:
        runs = cs["measured_runs_ns"]
        classes.append({
            "class_id": cs["class_id"],
            "weight_ppm": cs["weight_ppm"],
            "median_ns": stats.median_u64(runs),
            "mad_ns": stats.mad_u64(runs),
            "min_ns": min(runs),
            "max_ns": max(runs),
            "measured_runs": len(runs),
            "cold_ns": stats.median_u64(cs["cold_runs_ns"]) if cs["cold_runs_ns"] else None,
            "fresh_ns": cs["fresh_runs_ns"],
            "verify_median_ns": stats.median_u64(cs["verify_runs_ns"]),
            "proof_bytes_max": cs["proof_bytes_max"],
            # cost_v1 components (§14.3): per measured run, Σ over the batch
            "verify_runs_ns": cs["measured_verify_runs_ns"],
            "proof_bytes_runs": cs["measured_proof_bytes_runs"],
            "verify_run_median_ns": stats.median_u64(cs["measured_verify_runs_ns"]),
            "verify_stat_ns": cost.verify_stat(a.verify_statistic, cs["measured_verify_runs_ns"]),
            "proof_bytes_run_median": stats.median_u64(cs["measured_proof_bytes_runs"]),
            "peak_rss_bytes": cs["peak_rss_bytes"],
            "outliers": cs["outliers"],
            "tripwire": cs["tripwire"],
        })
    summary = {
        "schema": "arena-baseline-summary-v1",
        "status": "DEV-HOST MEASUREMENT — not governed hardware, not an official number",
        "challenge_id": chal_id,
        "invocation_mode": s["procedure"].get("invocation_mode") or "vm_per_invocation",
        "challenge_name": chal["name"],
        "suite_revision": chal["workload_suite"]["revision"],
        "hardware_profile_of_challenge": chal["hardware_profile"],
        "measured_on": hw_label,
        "host_warnings": hp["warnings"],
        "started_at": started,
        "finished_at": finished,
        "reference_candidate": {
            "package_dir": rel,
            "git_tree": git_tree,
            "package_digest": package_digest,
            "entry_digests": entry,
            "bundle_tree_digest": s["bundle_tree_digest"],
        },
        "sandbox": s["sandbox"],
        "cpus": s["cpus"],
        "procedure": s["procedure"],
        "sampling": dict(s["sampling"], generators=gens, oracle_nearcore_pin=oracle_commit.strip().splitlines(),
                         note=("judge-secret HMAC sampling (season secret commitment "
                               + s["sampling"]["season_secret_commitment"] + "), as the live workers sample")
                         if s["sampling"].get("season_secret_commitment") else
                         "PUBLIC seeds derive_seed(...): reproducible by anyone; not the live (secret-seeded) procedure"),
        "schedule_seed": s["session"].get("schedule_seed"),
        "gates": {k: {"status": v["status"], "summary": v["summary"], "reason_codes": v["reason_codes"]} for k, v in gates.items()},
        "flags": s["session"]["flags"],
        "calibration": {
            "workload": cal["workload"],
            "pre_ns": cal["pre_ns"], "post_ns": cal["post_ns"],
            "pre_median_ns": dv.pre_median_ns, "post_median_ns": dv.post_median_ns,
            "session_drift_ppm": dv.session_drift_ppm, "pre_mad_ppm": dv.pre_mad_ppm, "post_mad_ppm": dv.post_mad_ppm,
            "ok": dv.ok, "reasons": list(dv.reasons),
            "note": "stand-in calibration workload; no governed reference median exists for this host",
        },
        "loadavg": s["loadavg"],
        "session_wall_secs": s["session_wall_secs"],
        "prepare_ns": s["job_result"]["benchmark"]["prepare_ns"] if s["job_result"].get("benchmark") else None,
        "native_verifier": s["native_verifier"],
        "fc_deps": s["fc_deps"],
        "classes": classes,
        "baseline_ns": [[c["class_id"], c["median_ns"]] for c in sorted(classes, key=lambda c: c["class_id"])],
        "package_rev": rev,
        "package_is_challenge_baseline_submission": package_digest == chal["workload_suite"]["baseline_submission"],
        "cost_baseline": [
            {"class_id": c["class_id"], "prove_ns": c["median_ns"], "verify_ns": c["verify_stat_ns"],
             "proof_bytes": c["proof_bytes_run_median"]}
            for c in sorted(classes, key=lambda c: c["class_id"])
        ],
        "verify_statistic": a.verify_statistic,
        "calibration_median_ns": stats.median_u64(cal["pre_ns"] + cal["post_ns"]),
        "verify_control": control_verdicts(classes, controls, a.verify_statistic,
                                           stats.median_u64(cal["pre_ns"] + cal["post_ns"])),
        "score_note": "the measured challenge has no baseline: the session is measured, not scored. Against these medians the reference scores exactly 100.000 by construction.",
    }
    json.dump(summary, open(os.path.join(out, "summary.json"), "w"), indent=1)
    open(os.path.join(out, "summary.json"), "a").write("\n")
    print(json.dumps({"package_digest": package_digest, "baseline_ns": summary["baseline_ns"],
                      "package_is_challenge_baseline_submission": summary["package_is_challenge_baseline_submission"],
                      "cost_baseline": summary["cost_baseline"],
                      "verify_control": [{k: v[k] for k in ("session", "ok", "reasons")} | {"drift_ppm": {c["class_id"]: c["drift_ppm"] for c in v["classes"]}}
                                         for v in summary["verify_control"]],
                      "calibration_ok": dv.ok, "flags": summary["flags"]}, indent=1))


if __name__ == "__main__":
    main()
