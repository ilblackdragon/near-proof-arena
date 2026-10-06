"""Offline cost_v1 re-scoring of existing benchmark sessions (BENCHMARK_SPEC §14.8).

Reads judge session artifacts (the worker's "benchmark session" JSON, as kept
in the object store) of admitted submissions and re-scores them under a price
model. Nothing is signed or published, the runs are not touched; results are
labelled OFFLINE.

Reference cost components (per class, per batch of `batch_size` requests):

* prove  — the challenge's frozen `workload_suite.baseline_ns` (the rule of
  §14.6: one reference session supplies both baselines, so the cost baseline's
  prove_ns is the speed baseline). The frozen baseline session must reproduce it.
* verify, bytes — from `--cost-baseline` (a `run_baseline.py` summary that
  re-measured the challenge's pinned `baseline_submission` with per-run
  verify / byte totals and passed the verify drift control, §14.4), or, without
  it, from the frozen baseline session (the 2026-10-05 draft procedure).

Per-run candidate components:

* verify per run is exact: `measured_verify_runs_ns` when the session has it,
  else the flat measured-phase verify list chunked by `batch_size`;
* proof bytes per run: exact (`measured_proof_bytes_runs`) only when the
  baseline and EVERY candidate have per-run totals; otherwise the upper bound
  `batch_size * proof_bytes_max` for all of them, baseline included.
"""

from __future__ import annotations

import json
from dataclasses import asdict, replace
from pathlib import Path

from .cost import Components, CostClassRuns, Prices, cost_bootstrap, cost_score, verify_control
from .score import ClassRuns, score_from_runs
from .seeds import derive_seed
from .stats import median_u64


def jcs_digest(obj) -> str:
    """sha256 of JCS(obj) for integer/string-only JSON (no floats)."""
    import hashlib

    b = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return "sha256:" + hashlib.sha256(b).hexdigest()


def _session_classes(session: dict) -> dict:
    s = session.get("session", session)
    return {c["class_id"]: c for c in s["classes"]}


def has_exact_bytes(session: dict) -> bool:
    return all(c.get("measured_proof_bytes_runs") for c in _session_classes(session).values())


def per_run(c: dict, batch_size: int, exact_bytes: bool) -> tuple[list[int], list[int], list[int]]:
    """(prove, verify, bytes) per measured run of one class of a session."""
    p = list(c["measured_runs_ns"])
    if c.get("measured_verify_runs_ns"):
        vr = list(c["measured_verify_runs_ns"])
    else:
        v = list(c["verify_runs_ns"])
        if len(v) != len(p) * batch_size:
            raise ValueError(f"{c['class_id']}: {len(v)} verify timings for {len(p)} runs x {batch_size}")
        vr = [sum(v[i * batch_size:(i + 1) * batch_size]) for i in range(len(p))]
    if exact_bytes:
        sr = list(c["measured_proof_bytes_runs"])
    else:
        sr = [batch_size * c["proof_bytes_max"]] * len(p)
    if not (len(p) == len(vr) == len(sr)):
        raise ValueError(f"{c['class_id']}: run length mismatch")
    return p, vr, sr


def _frozen(chal: dict) -> dict[str, int]:
    return dict((k, v) for k, v in chal["workload_suite"]["baseline_ns"])


def _batch_sizes(chal: dict) -> dict[str, int]:
    return {c["id"]: c["batch_size"] for c in chal["workload_suite"]["classes"]}


def baseline_components(
    chal: dict, baseline_session: dict, cost_baseline: dict | None, exact_bytes: bool, allow_unconfirmed: bool = False
) -> tuple[dict[str, Components], dict, dict[str, dict[str, Components]]]:
    """Reference components per class, plus the controls that justify them."""
    bs, frozen = _batch_sizes(chal), _frozen(chal)
    controls: dict = {}
    frozen_v = {}
    for cid, c in _session_classes(baseline_session).items():
        p, v, _ = per_run(c, bs[cid], False)
        if median_u64(p) != frozen[cid]:
            raise ValueError(f"{cid}: baseline session median {median_u64(p)} != frozen baseline_ns {frozen[cid]}")
        frozen_v[cid] = (v, c)
    controls["frozen_session_challenge_id"] = baseline_session.get("challenge_id")
    if cost_baseline is None:
        out = {}
        for cid, (v, c) in frozen_v.items():
            _, _, s = per_run(c, bs[cid], exact_bytes)
            out[cid] = Components(frozen[cid], median_u64(v), median_u64(s))
        return out, controls, {}
    if cost_baseline["challenge_id"] != chal.get("_id"):
        raise ValueError(f"cost baseline measured {cost_baseline['challenge_id']}, not {chal.get('_id')}")
    if not cost_baseline.get("package_is_challenge_baseline_submission"):
        raise ValueError("cost baseline did not measure the challenge's baseline_submission package")
    if cost_baseline["calibration"]["ok"] is not True or cost_baseline.get("flags"):
        raise ValueError("cost baseline session is infra-invalid (calibration / flags)")
    vc = cost_baseline.get("verify_control") or []
    valid = [x for x in vc if x.get("valid")]  # §6.1: infra-invalid controls do not count
    controls["confirmed"] = bool(valid) and all(x["ok"] for x in valid)
    if not controls["confirmed"] and not allow_unconfirmed:
        raise ValueError(f"cost baseline lacks a passing verify drift control: {[(x['session'], x.get('valid'), x['reasons']) for x in vc]}")
    out = {}
    cls = {c["class_id"]: c for c in cost_baseline["classes"]}
    for cid in sorted(cls):
        c = cls[cid]
        s = c["proof_bytes_runs"] if exact_bytes else [bs[cid] * c["proof_bytes_max"]] * len(c["proof_bytes_runs"])
        out[cid] = Components(frozen[cid], c["verify_run_median_ns"], median_u64(s))
    # the same reference as each valid control session measured it (same batches):
    # how far the score moves with the session the reference happens to be pinned from
    alts = {}
    for x in valid:
        vk = {k["class_id"]: k["control_verify_ns"] for k in x["classes"]}
        alts[x["session"]] = {
            cid: Components(frozen[cid], vk[cid], x["proof_bytes_run_median"][cid] if exact_bytes else out[cid].proof_bytes)
            for cid in out
        }
    # §6.2 prove control (informational here: the frozen prove_ns is used) and the
    # cross-window verify control against the frozen session of the same package
    controls["prove_vs_frozen_ppm"] = {
        cid: _ppm(frozen[cid], cls[cid]["median_ns"]) for cid in sorted(cls)
    }
    xw = verify_control({cid: median_u64(v) for cid, (v, _) in frozen_v.items()}, {cid: cls[cid]["verify_runs_ns"] for cid in cls})
    controls["verify_control_in_window"] = vc
    controls["verify_vs_frozen_session"] = {
        "ok": xw.ok,
        "reasons": list(xw.reasons),
        "classes": [asdict(c) for c in xw.classes],
        "note": "re-measured verify medians vs the frozen speed-baseline session (other day, same package and CPUs; batches are the same only if that session measured this challenge id); informational",
    }
    return out, controls, alts


def _ppm(a: int, b: int) -> int:
    from .calibration import drift_ppm

    return drift_ppm(a, b)


def rescore(
    chal: dict,
    pm: dict,
    baseline_session: dict,
    subs: list[tuple[dict, dict]],
    cost_baseline: dict | None = None,
    iterations: int = 10_000,
    allow_unconfirmed: bool = False,
) -> dict:
    hw_vcpus = chal["hardware_profile"]["vcpus"]
    prices = Prices.from_model(pm, hw_vcpus)
    exact = (cost_baseline is not None) and all(has_exact_bytes(s) for _, s in subs)
    base, controls, alts = baseline_components(chal, baseline_session, cost_baseline, exact, allow_unconfirmed)
    bs = _batch_sizes(chal)
    w = {c["id"]: c["weight_ppm"] for c in chal["workload_suite"]["classes"]}
    frozen = _frozen(chal)
    rows = []
    for view, session in subs:
        sc = _session_classes(session)
        runs, speed_runs = [], []
        for cid in sorted(sc):
            p, v, s = per_run(sc[cid], bs[cid], exact)
            runs.append(CostClassRuns(cid, w[cid], bs[cid], base[cid], tuple(p), tuple(v), tuple(s)))
            speed_runs.append(ClassRuns(cid, w[cid], frozen[cid], tuple(p)))
        prep = (view.get("benchmark") or {}).get("prepare_ns", 0)
        point = cost_score(prices, runs, prep, 0)
        seed = derive_seed("bootstrap", view["id"], "offline-cost-rescore")
        ci = cost_bootstrap(prices, runs, prep, 0, seed, iterations)
        sens = {label: cost_score(pr, runs, prep, 0).score_milli for label, pr in sensitivity(prices).items()}
        vs_ctl = {
            sess: cost_score(prices, [replace(r_, baseline=alt[r_.class_id]) for r_ in runs], prep, 0).score_milli
            for sess, alt in alts.items()
        }
        rows.append(
            {
                "submission_id": view["id"],
                "candidate": view.get("candidate_name"),
                "package_digest": view.get("package_digest"),
                "speed_score_milli_live": view.get("score_milli"),
                "speed_score_milli_recomputed": score_from_runs(speed_runs).score_milli,
                "cost_score_milli": point.score_milli,
                "cost_score_ci_milli": ci.half_width_milli,
                "sensitivity_cost_score_milli": sens,
                "cost_score_milli_vs_control_reference": vs_ctl,
                "classes": [
                    {
                        "class_id": c.class_id,
                        "weight_ppm": c.weight_ppm,
                        **{f"median_{k}": v for k, v in asdict(c.medians).items()},
                        **asdict(c.cost),
                        "baseline_total_fusd": c.baseline_total_fusd,
                    }
                    for c in point.classes
                ],
            }
        )
    from .cost import batch_cost

    baseline_rows = []
    for cid in sorted(base):
        b = batch_cost(prices, base[cid], 0, bs[cid])
        baseline_rows.append({"class_id": cid, **{f"median_{k}": v for k, v in asdict(base[cid]).items()}, **asdict(b)})
    approx = [
        "verify per run = exact sum of the run's verify wall times",
        "proof bytes per run = exact per-run totals (baseline and every candidate have them)"
        if exact
        else "proof bytes per run = batch_size x proof_bytes_max (some sessions predate per-run byte totals); same for baseline and candidates",
        f"verify was measured on the full {hw_vcpus}-CPU benchmark set = verifier_vcpus of this model ({pm['verifier_vcpus']})",
        "prepare not charged (prepare_amortization_requests = 0)",
    ]
    if cost_baseline is not None:
        approx.insert(0, "reference prove = frozen baseline_ns; reference verify / bytes = the re-measured cost baseline session ("
                      + cost_baseline["started_at"] + ", CPUs " + ",".join(map(str, cost_baseline["cpus"])) + ")")
    return {
        "schema": "arena-offline-cost-rescore-v1",
        "status": f"OFFLINE RE-SCORING under the {pm['status'].upper()} price model {pm['id']}@v{pm['version']}; no run is modified; not a board"
        + ("" if controls.get("confirmed", True) else "; reference verify UNCONFIRMED (VERIFY_DRIFT, BENCHMARK_SPEC 14.4): indicative only"),
        "challenge_id": chal.get("_id"),
        "challenge_name": chal["name"],
        "price_model_id": f"{pm['id']}@v{pm['version']}",
        "price_model_status": pm["status"],
        "price_model_digest": jcs_digest(pm),
        "prices": asdict(prices),
        "bytes_mode": "exact" if exact else "upper_bound",
        "approximations": approx,
        "cost_baseline_source": (
            {"summary": cost_baseline.get("_path"), "package_digest": cost_baseline["reference_candidate"]["package_digest"],
             "package_rev": cost_baseline.get("package_rev")}
            if cost_baseline is not None else {"session": "frozen speed-baseline session"}
        ),
        "controls": controls,
        "baseline": baseline_rows,
        "rows": rows,
    }


def sensitivity(p: Prices) -> dict[str, Prices]:
    return {
        "N_v=1": replace(p, validators_per_chunk=1),
        "N_v=84 (v1 draft)": replace(p, validators_per_chunk=84),
        "N_v=105": replace(p, validators_per_chunk=105),
        "bw=0": replace(p, bandwidth_fusd_per_byte=0),
        "bw=x1.8 (egress 0.09/GB)": replace(p, bandwidth_fusd_per_byte=p.bandwidth_fusd_per_byte * 9 // 5),
        "verify on 2 vCPUs (price only)": replace(p, verifier_vcpus=2),
    }


def _usd(fusd: int) -> str:
    return f"${fusd / 1e15:.6f}"


def markdown(r: dict) -> str:
    sens_keys = list(r["rows"][0]["sensitivity_cost_score_milli"])
    ctl_keys = list(r["rows"][0].get("cost_score_milli_vs_control_reference", {}))
    out = [
        f"# Offline cost_v1 re-scoring: {r['challenge_name']}",
        "",
        f"**{r['status']}.** Price model `{r['price_model_id']}` ({r['price_model_status']}), digest `{r['price_model_digest']}`.",
        "",
        "Prices: " + ", ".join(f"`{k}={v}`" for k, v in r["prices"].items()),
        "",
        "Approximations: " + "; ".join(r["approximations"]) + ".",
        "",
    ]
    c = r.get("controls") or {}
    if c:
        out += ["## Controls", ""]
        for v in c.get("verify_control_in_window", []):
            verdict = ("PASS" if v["ok"] else "FAIL " + ",".join(v["reasons"])) if v.get("valid") else (
                "not counted: session infra-invalid (" + ",".join(v.get("calibration_reasons") or v.get("flags") or []) + ")")
            out.append(
                f"* verify drift control `{v['session']}` vs the pinned session: **{verdict}** "
                f"(tolerance {v['tolerance_ppm']} ppm; " + ", ".join(f"{x['class_id']} {x['drift_ppm']} ppm" for x in v["classes"]) + ")"
            )
        x = c.get("verify_vs_frozen_session")
        if x:
            out.append(
                f"* verify vs the frozen speed-baseline session (other day; informational — not a paired control unless it sampled the same challenge id): {'within' if x['ok'] else 'outside'} tolerance ("
                + ", ".join(f"{k['class_id']} {k['control_verify_ns'] / 1e6:.1f} vs {k['pinned_verify_ns'] / 1e6:.1f} ms, {k['drift_ppm']} ppm" for k in x["classes"]) + ")"
            )
        if c.get("prove_vs_frozen_ppm"):
            out.append("* re-measured prove median vs frozen `baseline_ns` (§6.2, informational; the frozen value is used): "
                       + ", ".join(f"{k} {v} ppm" for k, v in c["prove_vs_frozen_ppm"].items()))
        out.append("")
    out += [
        "## Scores",
        "",
        "| candidate | submission | speed (live) | cost_v1 | cost CI ± | " + " | ".join([f"ref as in {k}" for k in ctl_keys] + sens_keys) + " |",
        "|---|---|---|---|---|" + "---|" * (len(ctl_keys) + len(sens_keys)),
    ]
    for row in sorted(r["rows"], key=lambda x: -x["cost_score_milli"]):
        extra = [row["cost_score_milli_vs_control_reference"][k] for k in ctl_keys] + [row["sensitivity_cost_score_milli"][k] for k in sens_keys]
        out.append(
            f"| {row['candidate']} | `{row['submission_id'][:12]}…` | {row['speed_score_milli_live'] / 1000:.3f} | "
            f"**{row['cost_score_milli'] / 1000:.3f}** | {row['cost_score_ci_milli'] / 1000:.3f} | " + " | ".join(f"{v / 1000:.3f}" for v in extra) + " |"
        )
    out += [
        "",
        "## Per-class cost per batch (USD; validator terms include N_v)",
        "",
        "| candidate | class | prove | N_v x verify | N_v x bandwidth | total | baseline total | verify ms/batch | proof KiB/batch |",
        "|---|---|---|---|---|---|---|---|---|",
    ]
    for b in r["baseline"]:
        out.append(
            f"| *reference (baseline)* | {b['class_id']} | {_usd(b['prove_fusd'])} | {_usd(b['verify_fusd'])} | {_usd(b['bandwidth_fusd'])} | "
            f"{_usd(b['total_fusd'])} | — | {b['median_verify_ns'] / 1e6:.1f} | {b['median_proof_bytes'] / 1024:.1f} |"
        )
    for row in r["rows"]:
        for c in row["classes"]:
            out.append(
                f"| {row['candidate']} | {c['class_id']} | {_usd(c['prove_fusd'])} | {_usd(c['verify_fusd'])} | {_usd(c['bandwidth_fusd'])} | "
                f"{_usd(c['total_fusd'])} | {_usd(c['baseline_total_fusd'])} | {c['median_verify_ns'] / 1e6:.1f} | {c['median_proof_bytes'] / 1024:.1f} |"
            )
    return "\n".join(out) + "\n"


def main(
    chal_path: str,
    pm_path: str,
    baseline_path: str,
    sub_paths: list[str],
    out_dir: str | None,
    cost_baseline_path: str | None = None,
    allow_unconfirmed: bool = False,
) -> dict:
    chal = json.loads(Path(chal_path).read_text())
    chal["_id"] = Path(chal_path).stem
    pm = json.loads(Path(pm_path).read_text())
    baseline = json.loads(Path(baseline_path).read_text())
    cb = None
    if cost_baseline_path:
        cb = json.loads(Path(cost_baseline_path).read_text())
        cb["_path"] = cost_baseline_path
    subs = []
    for p in sub_paths:
        view_path, session_path = p.split(":", 1)
        subs.append((json.loads(Path(view_path).read_text()), json.loads(Path(session_path).read_text())))
    r = rescore(chal, pm, baseline, subs, cb, allow_unconfirmed=allow_unconfirmed)
    if out_dir:
        d = Path(out_dir)
        d.mkdir(parents=True, exist_ok=True)
        (d / "rescore.json").write_text(json.dumps(r, indent=1) + "\n")
        (d / "README.md").write_text(markdown(r))
    return r
