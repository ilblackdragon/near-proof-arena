"""Generator for benchmarks/testvectors/score.json.

Inputs are hand-chosen; expected outputs come from the reference
implementation and are pinned in git. Tests check (a) the committed file
equals a fresh regeneration and (b) a set of hand-derived values, so a
regression in the reference cannot silently rewrite the vectors.

u64 values are JSON integers (serde_json reads them losslessly). f64 values
are strings in shortest round-trip form (Python repr / Rust `{}` Display).
"""

from __future__ import annotations

import json
import math

from .calibration import drift_ppm
from .outliers import flag_outliers
from .schedule import build_schedule
from .score import ClassInput, ClassRuns, ScoreError, bootstrap_ci, score
from .seeds import derive_seed
from .stats import SplitMix64, mad_u64, median_u64

SCHEMA = "arena-bench-testvectors-v1"


def _c(cid, w, base, med):
    return {"class_id": cid, "weight_ppm": w, "baseline_ns": base, "median_ns": med}


SCORE_CASES = [
    ("identity", [_c("a", 1_000_000, 1_000_000_000, 1_000_000_000)]),
    ("uniform_2x_faster", [_c("a", 500_000, 2_000, 1_000), _c("b", 500_000, 8_000_000, 4_000_000)]),
    ("opposite_cancel", [_c("a", 500_000, 2_000, 1_000), _c("b", 500_000, 1_000, 2_000)]),
    ("single_3x_slower", [_c("x", 1_000_000, 1_000_000, 3_000_000)]),
    (
        "three_class_realistic",
        [
            _c("transfer_small", 500_000, 1_840_211_337, 911_222_101),
            _c("transfer_large", 300_000, 12_904_000_113, 7_450_123_999),
            _c("create_account", 200_000, 2_350_777_002, 2_611_000_404),
        ],
    ),
    (
        "three_class_realistic_permuted",
        [
            _c("create_account", 200_000, 2_350_777_002, 2_611_000_404),
            _c("transfer_small", 500_000, 1_840_211_337, 911_222_101),
            _c("transfer_large", 300_000, 12_904_000_113, 7_450_123_999),
        ],
    ),
    ("uneven_ppm_weights", [_c("a", 1, 10, 1), _c("b", 333_333, 7_000, 9_000), _c("c", 666_666, 123_456_789, 98_765_432)]),
    ("big_ns_beyond_2p53", [_c("a", 1_000_000, 18_000_000_000_000_000_000, 9_007_199_254_740_993)]),
    ("1000x_speedup", [_c("a", 1_000_000, 3_600_000_000_000, 3_600_000_000)]),
    ("zero_weight_class_ignored", [_c("a", 0, 1, 1_000_000), _c("b", 1_000_000, 5_000, 4_000)]),
    ("utf8_order", [_c("Z", 250_000, 900, 1_000), _c("a", 250_000, 1_100, 1_000), _c("é", 500_000, 1_234, 1_000)]),
]

SCORE_ERROR_CASES = [
    ("empty", []),
    ("weights_sum_low", [_c("a", 999_999, 1, 1)]),
    ("weights_sum_high", [_c("a", 600_000, 1, 1), _c("b", 400_001, 1, 1)]),
    ("zero_candidate_time", [_c("a", 1_000_000, 1, 0)]),
    ("zero_baseline_time", [_c("a", 1_000_000, 0, 1)]),
    ("duplicate_class", [_c("a", 500_000, 1, 1), _c("a", 500_000, 1, 1)]),
    ("overflow", [_c("a", 1_000_000, 18_446_744_073_709_551_615, 1)]),
]


def _r(cid, w, base, runs):
    return {"class_id": cid, "weight_ppm": w, "baseline_ns": base, "runs_ns": runs}


BOOTSTRAP_CASES = [
    ("constant_runs", 1, 200, [_r("a", 1_000_000, 1_000, [500, 500, 500, 500, 500])]),
    (
        "two_class_noisy",
        42,
        500,
        [
            _r("a", 600_000, 1_000_000, [480_000, 510_000, 495_000, 530_000, 470_000, 505_000, 499_000]),
            _r("b", 400_000, 9_000_000, [9_100_000, 8_700_000, 9_400_000, 8_950_000, 9_020_000, 12_000_000]),
        ],
    ),
    (
        "seed_from_derive",
        derive_seed("bootstrap", "sub_0123456789abcdef", "sha256:" + "ab" * 32),
        1_000,
        [_r("k", 1_000_000, 7_777, [7_000, 7_100, 6_900, 7_050, 6_950, 7_400, 6_800, 7_020, 7_010])],
    ),
]

MEDIAN_CASES = [[7], [3, 1], [1, 2, 3, 4], [5, 1, 9, 3, 7], [10, 10, 10, 1_000], [18_446_744_073_709_551_615, 18_446_744_073_709_551_613], [1, 2, 100, 101, 102, 103]]

SPLITMIX_SEEDS = [0, 1, 0x9E3779B97F4A7C15, 18_446_744_073_709_551_615]

SEED_CASES = [
    ("schedule", ["chl_00112233445566778899aabbccddeeff", "sub_0123456789abcdef", "1"]),
    ("bootstrap", ["sub_0123456789abcdef", "sha256:" + "ab" * 32]),
    ("x", []),
]

SCHEDULE_CASES = [
    {"class_ids": ["c", "a", "b"], "seed": 7, "cold_runs": 1, "warmup_runs": 1, "measured_runs": 3, "fresh_confirm_runs": 1, "calibration_runs": 2},
    {"class_ids": ["only"], "seed": 0, "cold_runs": 0, "warmup_runs": 0, "measured_runs": 2, "fresh_confirm_runs": 0, "calibration_runs": 0},
]

OUTLIER_CASES = [
    ([100, 101, 99, 100, 150], 3),
    ([100, 100, 100, 100, 101], 5),
    ([1_000, 1_010, 990, 1_005, 995, 1_500, 600], 3),
]

DRIFT_CASES = [(1_000, 1_000), (1_000, 1_020), (1_000, 1_021), (1_000, 979), (3, 4)]


def _score_expect(classes):
    try:
        res = score([ClassInput(**c) for c in classes])
    except ScoreError as e:
        return {"error": e.code}
    # Portability guard: ln/exp may differ by a few ulp across libms, so the
    # rounding point must be far (relative 1e-12, ~4500 ulp) from a .5 milli boundary.
    m = res.score_f64 * 1000.0
    frac = m - math.floor(m)
    assert abs(frac - 0.5) > max(1e-6, m * 1e-12), "vector too close to a rounding boundary"
    return {"score_milli": res.score_milli, "score_f64": repr(res.score_f64)}


def generate() -> dict:
    vec: dict = {
        "schema": SCHEMA,
        "spec": "docs/BENCHMARK_SPEC.md §8",
        "score_f64_rel_tolerance": "1e-12",
        "notes": "Integer fields must match exactly. score_f64 is informative (shortest round-trip f64).",
    }
    out = []
    for s in SPLITMIX_SEEDS:
        r = SplitMix64(s)
        out.append({"seed": s, "outputs": [r.next_u64() for _ in range(5)]})
    vec["splitmix64"] = out
    vec["median_mad"] = [{"input": xs, "median": median_u64(xs), "mad": mad_u64(xs)} for xs in MEDIAN_CASES]
    vec["derive_seed"] = [{"purpose": p, "parts": parts, "seed": derive_seed(p, *parts)} for p, parts in SEED_CASES]
    vec["score"] = [{"name": n, "classes": cs, "expect": _score_expect(cs)} for n, cs in SCORE_CASES + SCORE_ERROR_CASES]
    bs = []
    for name, seed, iters, classes in BOOTSTRAP_CASES:
        r = bootstrap_ci([ClassRuns(c["class_id"], c["weight_ppm"], c["baseline_ns"], tuple(c["runs_ns"])) for c in classes], seed, iters)
        bs.append(
            {
                "name": name,
                "seed": seed,
                "iterations": iters,
                "classes": classes,
                "expect": {"score_milli": r.score_milli, "lo_milli": r.lo_milli, "hi_milli": r.hi_milli, "half_width_milli": r.half_width_milli},
            }
        )
    bs.append({"name": "no_runs", "seed": 1, "iterations": 10, "classes": [_r("a", 1_000_000, 1, [])], "expect": {"error": "NO_RUNS"}})
    vec["bootstrap"] = bs
    vec["schedule"] = [
        {**case, "expect": [[e.phase, e.class_id, e.round] for e in build_schedule(**case)]} for case in SCHEDULE_CASES
    ]
    vec["outliers"] = []
    for runs, k in OUTLIER_CASES:
        o = flag_outliers(runs, k)
        vec["outliers"].append({"runs_ns": runs, "k": k, "expect": {"median_ns": o.median_ns, "mad_ns": o.mad_ns, "flagged_indices": list(o.flagged_indices)}})
    vec["drift_ppm"] = [{"a": a, "b": b, "ppm": drift_ppm(a, b)} for a, b in DRIFT_CASES]
    return vec


def dumps(vec: dict) -> str:
    return json.dumps(vec, indent=1, ensure_ascii=False) + "\n"
