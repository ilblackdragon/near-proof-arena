"""Offline cost_v1 re-scoring of existing benchmark sessions (BENCHMARK_SPEC §14.6).

Reads judge session artifacts (the worker's "benchmark session" JSON: per
class `measured_runs_ns`, the flat `verify_runs_ns` of the measured runs in
schedule order, `proof_bytes_max`) and re-scores them under a price model.
Nothing is signed or published; results are labelled OFFLINE.

Older sessions have no per-run proof-byte totals, so the bytes component is
reconstructed as `batch_size * proof_bytes_max` (an upper bound, identical
treatment for baseline and candidates). Per-run verify totals are exact: the
flat list is chunked by `batch_size` (one chunk per measured run).
"""

from __future__ import annotations

import json
from dataclasses import asdict, replace
from pathlib import Path

from .cost import Components, CostClassRuns, Prices, cost_bootstrap, cost_score
from .score import ClassRuns, score_from_runs
from .seeds import derive_seed


def jcs_digest(obj) -> str:
    """sha256 of JCS(obj) for integer/string-only JSON (no floats)."""
    import hashlib

    b = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return "sha256:" + hashlib.sha256(b).hexdigest()


def _session_classes(session: dict) -> dict:
    s = session.get("session", session)
    return {c["class_id"]: c for c in s["classes"]}


def per_run(c: dict, batch_size: int) -> tuple[list[int], list[int], list[int]]:
    p = list(c["measured_runs_ns"])
    v = list(c["verify_runs_ns"])
    if len(v) != len(p) * batch_size:
        raise ValueError(f"{c['class_id']}: {len(v)} verify timings for {len(p)} runs x {batch_size}")
    vr = [sum(v[i * batch_size:(i + 1) * batch_size]) for i in range(len(p))]
    sr = [batch_size * c["proof_bytes_max"]] * len(p)
    return p, vr, sr


def baseline_components(chal: dict, baseline_session: dict) -> dict[str, Components]:
    bs = {c["id"]: c["batch_size"] for c in chal["workload_suite"]["classes"]}
    frozen = dict((k, v) for k, v in chal["workload_suite"]["baseline_ns"])
    from .stats import median_u64

    out = {}
    for cid, c in _session_classes(baseline_session).items():
        p, v, s = per_run(c, bs[cid])
        if median_u64(p) != frozen[cid]:
            raise ValueError(f"{cid}: baseline session median {median_u64(p)} != frozen baseline_ns {frozen[cid]}")
        out[cid] = Components(median_u64(p), median_u64(v), median_u64(s))
    return out


def rescore(chal: dict, pm: dict, baseline_session: dict, subs: list[tuple[dict, dict]], iterations: int = 10_000) -> dict:
    hw_vcpus = chal["hardware_profile"]["vcpus"]
    prices = Prices.from_model(pm, hw_vcpus)
    base = baseline_components(chal, baseline_session)
    bs = {c["id"]: c["batch_size"] for c in chal["workload_suite"]["classes"]}
    w = {c["id"]: c["weight_ppm"] for c in chal["workload_suite"]["classes"]}
    frozen = dict((k, v) for k, v in chal["workload_suite"]["baseline_ns"])
    rows = []
    for view, session in subs:
        sc = _session_classes(session)
        runs = []
        speed_runs = []
        for cid in sorted(sc):
            p, v, s = per_run(sc[cid], bs[cid])
            runs.append(CostClassRuns(cid, w[cid], bs[cid], base[cid], tuple(p), tuple(v), tuple(s)))
            speed_runs.append(ClassRuns(cid, w[cid], frozen[cid], tuple(p)))
        prep = (view.get("benchmark") or {}).get("prepare_ns", 0)
        point = cost_score(prices, runs, prep, 0)
        seed = derive_seed("bootstrap", view["id"], "offline-cost-rescore")
        ci = cost_bootstrap(prices, runs, prep, 0, seed, iterations)
        sens = {}
        for label, pr in sensitivity(prices).items():
            sens[label] = cost_score(pr, runs, prep, 0).score_milli
        rows.append(
            {
                "submission_id": view["id"],
                "candidate": view.get("candidate_name"),
                "speed_score_milli_live": view.get("score_milli"),
                "speed_score_milli_recomputed": score_from_runs(speed_runs).score_milli,
                "cost_score_milli": point.score_milli,
                "cost_score_ci_milli": ci.half_width_milli,
                "sensitivity_cost_score_milli": sens,
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
    baseline_rows = []
    for cid in sorted(base):
        from .cost import batch_cost

        b = batch_cost(prices, base[cid], 0, bs[cid])
        baseline_rows.append({"class_id": cid, **{f"median_{k}": v for k, v in asdict(base[cid]).items()}, **asdict(b)})
    return {
        "schema": "arena-offline-cost-rescore-v1",
        "status": "OFFLINE RE-SCORING under a DRAFT price model; not signed, not published, not a board",
        "challenge_id": chal.get("_id"),
        "challenge_name": chal["name"],
        "price_model_id": f"{pm['id']}@v{pm['version']}",
        "price_model_status": pm["status"],
        "price_model_digest": jcs_digest(pm),
        "prices": asdict(prices),
        "approximations": [
            "proof bytes per run = batch_size x proof_bytes_max (sessions predate per-run byte totals); same for baseline and candidates",
            "verify per run = exact sum of the run's verify wall times (flat verify_runs_ns chunked by batch_size)",
            "verify was measured on the full 8-CPU benchmark set = verifier_vcpus of this model",
            "prepare not charged (prepare_amortization_requests = 0)",
        ],
        "baseline": baseline_rows,
        "rows": rows,
    }


def sensitivity(p: Prices) -> dict[str, Prices]:
    return {
        "N_v=1": replace(p, validators_per_chunk=1),
        "N_v=30": replace(p, validators_per_chunk=30),
        "N_v=105": replace(p, validators_per_chunk=105),
        "bw=0": replace(p, bandwidth_fusd_per_byte=0),
        "bw=x1.8 (egress 0.09/GB)": replace(p, bandwidth_fusd_per_byte=p.bandwidth_fusd_per_byte * 9 // 5),
        "verify on 2 vCPUs (price only)": replace(p, verifier_vcpus=2),
    }


def _usd(fusd: int) -> str:
    return f"${fusd / 1e15:.6f}"


def markdown(r: dict) -> str:
    out = [
        f"# Offline cost_v1 re-scoring: {r['challenge_name']}",
        "",
        f"**{r['status']}.** Price model `{r['price_model_id']}` ({r['price_model_status']}), digest `{r['price_model_digest']}`.",
        "",
        "Prices: " + ", ".join(f"`{k}={v}`" for k, v in r["prices"].items()),
        "",
        "Approximations: " + "; ".join(r["approximations"]) + ".",
        "",
        "## Scores",
        "",
        "| candidate | submission | speed (live) | cost_v1 | cost CI ± | " + " | ".join(r["rows"][0]["sensitivity_cost_score_milli"]) + " |",
        "|---|---|---|---|---|" + "---|" * len(r["rows"][0]["sensitivity_cost_score_milli"]),
    ]
    for row in sorted(r["rows"], key=lambda x: -x["cost_score_milli"]):
        sens = " | ".join(f"{v / 1000:.3f}" for v in row["sensitivity_cost_score_milli"].values())
        out.append(
            f"| {row['candidate']} | `{row['submission_id'][:12]}…` | {row['speed_score_milli_live'] / 1000:.3f} | "
            f"**{row['cost_score_milli'] / 1000:.3f}** | {row['cost_score_ci_milli'] / 1000:.3f} | {sens} |"
        )
    out += [
        "",
        "## Per-class cost per batch of 8 requests (USD; validator terms include N_v)",
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


def main(chal_path: str, pm_path: str, baseline_path: str, sub_paths: list[str], out_dir: str | None) -> dict:
    chal = json.loads(Path(chal_path).read_text())
    chal["_id"] = Path(chal_path).stem
    pm = json.loads(Path(pm_path).read_text())
    baseline = json.loads(Path(baseline_path).read_text())
    subs = []
    for p in sub_paths:
        view_path, session_path = p.split(":", 1)
        subs.append((json.loads(Path(view_path).read_text()), json.loads(Path(session_path).read_text())))
    r = rescore(chal, pm, baseline, subs)
    if out_dir:
        d = Path(out_dir)
        d.mkdir(parents=True, exist_ok=True)
        (d / "rescore.json").write_text(json.dumps(r, indent=1) + "\n")
        (d / "README.md").write_text(markdown(r))
    return r
