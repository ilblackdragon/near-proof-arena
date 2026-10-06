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


# ---- cost_v1 (docs/BENCHMARK_SPEC.md §14) -> benchmarks/testvectors/cost.json ----

COST_SCHEMA = "arena-bench-cost-testvectors-v1"

_PM = {
    "validators_per_chunk": 105,
    "prover_vcpus": 8,
    "verifier_vcpus": 8,
    "cpu_fusd_per_vcpu_second": 7_610_000_000,
    "bandwidth_fusd_per_byte": 83_500,
    "storage_fusd_per_byte": 0,
    "prepare_amortization_requests": 0,
}


def _cr(cid, w, base, p, v, s, batch=8):
    return {
        "class_id": cid,
        "weight_ppm": w,
        "batch_size": batch,
        "baseline": {"prove_ns": base[0], "verify_ns": base[1], "proof_bytes": base[2]},
        "prove_runs_ns": p,
        "verify_runs_ns": v,
        "proof_bytes_runs": s,
    }


_REEXEC_256 = (10_205_590, 1_317_280_576, 669_352)

COST_BATCH_CASES = [
    ("ns_rounding_up", _PM, {"prove_ns": 1, "verify_ns": 1, "proof_bytes": 0}, 0, 8),
    ("reexec_like", _PM, {"prove_ns": 10_205_590, "verify_ns": 1_317_280_576, "proof_bytes": 669_352}, 0, 8),
    ("stark_like", _PM, {"prove_ns": 62_156_378_513, "verify_ns": 6_212_980_976, "proof_bytes": 24_620_920}, 6_625_675, 8),
    ("prepare_amortized", {**_PM, "prepare_amortization_requests": 43_200, "storage_fusd_per_byte": 7}, {"prove_ns": 5_000_000, "verify_ns": 9_000_000, "proof_bytes": 100_000}, 600_000_000_000, 16),
    ("bad_prices", {**_PM, "validators_per_chunk": 0}, {"prove_ns": 1, "verify_ns": 1, "proof_bytes": 1}, 0, 1),
    ("zero_verify", _PM, {"prove_ns": 1, "verify_ns": 0, "proof_bytes": 1}, 0, 1),
    ("overflow_u64", _PM, {"prove_ns": 18_446_744_073_709_551_615, "verify_ns": 1, "proof_bytes": 1}, 0, 1),
    ("overflow_u128_intermediate", {**_PM, "bandwidth_fusd_per_byte": 18_446_744_073_709_551_615, "validators_per_chunk": 4_294_967_295}, {"prove_ns": 1, "verify_ns": 1, "proof_bytes": 18_446_744_073_709_551_615}, 0, 1),
    ("free_bytes", {**_PM, "bandwidth_fusd_per_byte": 0}, {"prove_ns": 1, "verify_ns": 1, "proof_bytes": 0}, 0, 1),
]

COST_SCORE_CASES = [
    ("baseline_is_100", _PM, 0, 0, [_cr("batch-256", 1_000_000, _REEXEC_256, [10_205_590, 9_900_000, 10_500_000], [1_317_280_576, 1_300_000_000, 1_330_000_000], [669_352, 669_352, 669_352])]),
    (
        "v1_6_shape_stark_vs_reexec",
        _PM,
        6_625_675,
        0,
        [
            _cr("batch-1", 200_000, (6_211_419, 38_512_968, 8_704), [1_989_271_600, 2_039_539_650, 2_044_468_726], [3_451_930_376, 3_480_000_000, 3_420_000_000], [15_643_512, 15_643_512, 15_643_512]),
            _cr("batch-16", 300_000, (6_876_460, 142_200_576, 59_256), [6_492_014_396, 6_500_000_000, 6_480_000_000], [4_577_845_320, 4_600_000_000, 4_560_000_000], [19_688_376, 19_688_376, 19_688_376]),
            _cr("batch-256", 500_000, _REEXEC_256, [62_156_378_513, 62_000_000_000, 62_300_000_000], [6_212_980_976, 6_250_000_000, 6_200_000_000], [24_620_920, 24_620_920, 24_620_920]),
        ],
    ),
    (
        "smaller_proof_faster_verify_wins",
        {**_PM, "validators_per_chunk": 60},
        0,
        0,
        [
            _cr("a", 400_000, (1_000_000, 50_000_000, 80_000), [3_000_000, 2_900_000, 3_100_000, 3_050_000, 2_950_000], [5_000_000, 5_100_000, 4_900_000, 5_200_000, 4_800_000], [12_000, 12_000, 12_000, 12_000, 12_000]),
            _cr("b", 600_000, (2_000_000, 400_000_000, 700_000), [9_000_000, 9_100_000, 8_900_000, 9_300_000, 8_700_000], [6_000_000, 6_100_000, 5_900_000, 6_050_000, 5_950_000], [12_500, 12_500, 12_400, 12_500, 12_600]),
        ],
    ),
    ("no_runs", _PM, 0, 0, [_cr("a", 1_000_000, (1, 1, 1), [], [], [])]),
    ("run_length_mismatch", _PM, 0, 0, [_cr("a", 1_000_000, (1, 1, 1), [1, 2], [1], [1, 1])]),
    ("weight_sum", _PM, 0, 0, [_cr("a", 999_999, (1, 1, 1), [1], [1], [1])]),
    ("empty", _PM, 0, 0, []),
]

# bench-spec-v1.4: V = lower quartile of the per-run verify totals (v1-6 batch-16 shape: bimodal)
_PM_LQ = {**_PM, "validators_per_chunk": 50, "verify_statistic": "lower_quartile"}
_BIMODAL_16 = [151_821_275, 189_491_143, 151_863_038, 150_586_441, 164_231_934, 184_073_834, 184_274_509, 152_006_839,
               193_160_053, 215_278_709, 153_381_162, 200_374_542, 150_781_531, 151_936_626, 210_023_395]
COST_SCORE_CASES += [
    (
        "lower_quartile_bimodal_verify",
        _PM_LQ,
        0,
        0,
        [
            _cr("batch-16", 400_000, (7_396_337, 151_863_038, 48_164), [7_400_000 + 1_000 * i for i in range(15)], _BIMODAL_16, [48_164] * 15),
            _cr("batch-1", 600_000, (6_967_862, 38_000_000, 6_249), [6_900_000, 7_000_000, 6_950_000, 7_050_000], [39_000_000, 37_900_000, 41_000_000, 38_100_000], [6_249, 6_300, 6_249, 6_249]),
        ],
    ),
    ("lower_quartile_even_runs", _PM_LQ, 0, 0, [_cr("a", 1_000_000, (100, 1_000, 10), [100, 100, 100, 100, 100, 100, 100, 100], [990, 2_000, 1_010, 3_000, 1_000, 5_000, 995, 4_000], [10] * 8)]),
]

# bench-spec-v1.6: paired baseline control. The reference runs on the same batches; its runs
# replace the pinned baseline (kept as a deliberately wrong value: it must not be used).
def _pcr(cid, w, p, v, s, rp, rv, rs, bs=8):
    return {**_cr(cid, w, (1, 1, 1), p, v, s), "batch_size": bs,
            "paired": {"prove_runs_ns": rp, "verify_runs_ns": rv, "proof_bytes_runs": rs}}


_PM_PAIRED = {**_PM_LQ}
COST_SCORE_CASES += [
    (
        "paired_self_is_100",
        _PM_PAIRED,
        0,
        0,
        [_pcr("d0-quiet", 1_000_000, [7_000_000, 6_900_000, 7_100_000, 7_050_000], [880_000_000, 900_000_000, 870_000_000, 950_000_000],
              [17_296] * 4, [7_000_000, 6_900_000, 7_100_000, 7_050_000], [880_000_000, 900_000_000, 870_000_000, 950_000_000], [17_296] * 4)],
    ),
    (
        "paired_heavy_tailed_inputs",
        _PM_PAIRED,
        0,
        0,
        [
            # the candidate drew two 320 ms chunks; so did the reference on the same batch
            _pcr("d0-quiet", 400_000, [6_500_000, 6_600_000, 6_400_000, 6_700_000, 6_550_000], [700_000_000, 710_000_000, 690_000_000, 720_000_000, 705_000_000],
                 [17_000] * 5, [7_100_000, 7_000_000, 7_200_000, 7_050_000, 7_150_000], [800_000_000, 815_000_000, 790_000_000, 830_000_000, 805_000_000], [17_296] * 5),
            _pcr("d0-missing", 600_000, [6_900_000, 7_000_000, 6_950_000, 7_050_000, 6_980_000], [1_100_000_000, 1_150_000_000, 1_120_000_000, 1_090_000_000, 1_130_000_000],
                 [34_000] * 5, [7_200_000, 7_100_000, 7_300_000, 7_250_000, 7_150_000], [1_113_000_000, 1_140_000_000, 1_120_000_000, 1_150_000_000, 1_125_000_000], [34_439] * 5),
        ],
    ),
    ("paired_length_mismatch", _PM_PAIRED, 0, 0, [_pcr("a", 1_000_000, [1, 2], [1, 1], [1, 1], [1], [1, 1], [1, 1])]),
]

COST_BOOTSTRAP_CASES = [
    ("v1_6_shape", 4242, 300, COST_SCORE_CASES[1]),
    ("two_class_noisy", derive_seed("bootstrap", "sub_0123456789abcdef", "run_0123456789abcdef"), 500, COST_SCORE_CASES[2]),
    ("lower_quartile_bimodal", 99, 400, COST_SCORE_CASES[-5]),
    ("paired_heavy_tailed", 7, 400, COST_SCORE_CASES[-2]),
]

# (name, probes in time order, max_step_ppm, max_noise_ppm, reference (ns, max_ppm) or None)
CALIBRATION_PROBE_CASES = [
    ("steady", [450_000_000, 451_000_000, 449_000_000, 452_000_000, 450_500_000, 451_500_000], 20_000, 50_000, None),
    ("slow_drift_passes", [450_000_000 + 4_000_000 * i for i in range(12)], 20_000, 50_000, None),
    ("one_step_between_rounds_passes", [450_000_000] * 5 + [480_000_000] * 5, 20_000, 50_000, None),
    ("oscillating_fails_step", [450_000_000, 480_000_000] * 5, 20_000, 50_000, None),
    ("noisy", [400_000_000, 500_000_000, 420_000_000, 480_000_000, 410_000_000, 490_000_000], 300_000, 50_000, None),
    ("reference_drift", [450_000_000, 451_000_000, 452_000_000], 20_000, 50_000, (400_000_000, 50_000)),
    ("reference_ok", [450_000_000, 451_000_000, 452_000_000], 20_000, 50_000, (440_000_000, 50_000)),
    ("too_few", [450_000_000], 20_000, 50_000, None),
    ("zero", [450_000_000, 0], 20_000, 50_000, None),
    # live host, CPUs 0-7, 2026-10-06 18:10 UTC: 29 probes of 3 warm runs each (ms → ns)
    ("live_cpus0_7_noise_only", [int(x * 1_000_000) for x in (575.0, 572.0, 551.4, 558.7, 580.3, 553.8, 555.6, 560.9, 535.5, 570.7, 578.1, 568.2, 570.4, 568.4, 556.0, 584.0, 552.2, 562.2, 562.9, 544.0, 535.0, 592.0, 553.0, 544.5, 543.5, 578.0, 529.7, 545.0, 574.3)], 20_000, 50_000, None),
    ("two_probes", [450_000_000, 460_000_000], 20_000, 50_000, None),
]

# (name, pinned {class: verify_ns}, control {class: [per-run verify totals]}, tolerance_ppm)
VERIFY_CONTROL_CASES = [
    ("within_tolerance", {"b": 2_000_000, "a": 1_000_000}, {"a": [1_030_000, 990_000, 1_000_000], "b": [2_050_000, 2_060_000, 1_990_000]}, 30_000),
    ("exactly_at_tolerance_up", {"a": 1_000_000}, {"a": [1_030_000]}, 30_000),
    ("exactly_at_tolerance_down", {"a": 1_000_000}, {"a": [970_000]}, 30_000),
    ("one_ns_over", {"a": 1_000_000}, {"a": [1_030_001]}, 30_000),
    ("rounds_up", {"a": 3}, {"a": [4, 4]}, 333_333),
    ("one_class_drifts", {"d0-quiet": 47_330_387, "d0-transfers": 52_000_000}, {"d0-quiet": [47_000_000, 47_500_000], "d0-transfers": [56_000_000, 57_000_000, 55_000_000]}, 30_000),
    ("even_count_median", {"a": 100}, {"a": [90, 100, 104, 200]}, 30_000),
    ("class_mismatch", {"a": 1}, {"b": [1]}, 30_000),
    ("no_runs", {"a": 1}, {"a": []}, 30_000),
    ("zero_pinned", {"a": 0}, {"a": [1]}, 30_000),
]
# (name, pinned, control, tolerance_ppm, verify_statistic): the v1-6 batch-16 sessions of 2026-10-06
VERIFY_CONTROL_STAT_CASES = [
    ("lower_quartile_bimodal_passes", {"batch-16": 151_863_038}, {"batch-16": [183_000_000, 181_000_000, 191_000_000, 154_000_000, 181_000_000, 177_000_000, 156_000_000, 198_000_000, 152_000_000, 153_500_000, 194_000_000, 205_000_000, 154_500_000, 207_000_000, 226_000_000]}, 30_000, "lower_quartile"),
    ("median_bimodal_fails", {"batch-16": 164_231_934}, {"batch-16": [183_000_000, 181_000_000, 191_000_000, 154_000_000, 181_000_000, 177_000_000, 156_000_000, 198_000_000, 152_000_000, 153_500_000, 194_000_000, 205_000_000, 154_500_000, 207_000_000, 226_000_000]}, 30_000, "median"),
    ("lower_quartile_index", {"a": 100}, {"a": [500, 400, 300, 200, 103, 101, 99]}, 30_000, "lower_quartile"),
]


def _prices(pm):
    from .cost import Prices

    return Prices(**pm)


def _breakdown_json(b):
    return {
        "prove_fusd": b.prove_fusd,
        "prepare_fusd": b.prepare_fusd,
        "verify_fusd": b.verify_fusd,
        "bandwidth_fusd": b.bandwidth_fusd,
        "storage_fusd": b.storage_fusd,
        "total_fusd": b.total_fusd,
    }


def generate_cost() -> dict:
    from .cost import Components, CostError, batch_cost, class_runs_from_json, cost_bootstrap, cost_score, verify_control

    vec: dict = {
        "schema": COST_SCHEMA,
        "spec": "docs/BENCHMARK_SPEC.md §14",
        "notes": "All outputs are integers and must match exactly. Units: ns, bytes, femto-USD.",
    }
    out = []
    for name, pm, comp, prep, bs in COST_BATCH_CASES:
        try:
            exp = _breakdown_json(batch_cost(_prices(pm), Components(**comp), prep, bs))
        except CostError as e:
            exp = {"error": e.code}
        out.append({"name": name, "prices": pm, "components": comp, "prepare_ns": prep, "batch_size": bs, "expect": exp})
    vec["batch_cost"] = out
    out = []
    for name, pm, prep, bprep, classes in COST_SCORE_CASES:
        try:
            r = cost_score(_prices(pm), class_runs_from_json(classes), prep, bprep)
            m = r.score_f64 * 1000.0
            frac = m - math.floor(m)
            assert abs(frac - 0.5) > max(1e-6, m * 1e-12), f"{name}: too close to a rounding boundary"
            exp = {
                "score_milli": r.score_milli,
                "classes": [
                    {"class_id": c.class_id, "baseline_total_fusd": c.baseline_total_fusd, **_breakdown_json(c.cost)} for c in r.classes
                ],
            }
        except CostError as e:
            exp = {"error": e.code}
        except ScoreError as e:
            exp = {"error": e.code}
        out.append({"name": name, "prices": pm, "prepare_ns": prep, "baseline_prepare_ns": bprep, "classes": classes, "expect": exp})
    vec["cost_score"] = out
    out = []
    for name, seed, iters, (_, pm, prep, bprep, classes) in COST_BOOTSTRAP_CASES:
        r = cost_bootstrap(_prices(pm), class_runs_from_json(classes), prep, bprep, seed, iters)
        out.append(
            {
                "name": name,
                "seed": seed,
                "iterations": iters,
                "prices": pm,
                "prepare_ns": prep,
                "baseline_prepare_ns": bprep,
                "classes": classes,
                "expect": {"score_milli": r.score_milli, "lo_milli": r.lo_milli, "hi_milli": r.hi_milli, "half_width_milli": r.half_width_milli},
            }
        )
    vec["cost_bootstrap"] = out
    out = []
    for name, pinned, control, tol in VERIFY_CONTROL_CASES:
        try:
            r = verify_control(pinned, control, tol)
            exp = {
                "ok": r.ok,
                "reasons": list(r.reasons),
                "classes": [
                    {"class_id": c.class_id, "pinned_verify_ns": c.pinned_verify_ns, "control_verify_ns": c.control_verify_ns, "drift_ppm": c.drift_ppm, "ok": c.ok}
                    for c in r.classes
                ],
            }
        except CostError as e:
            exp = {"error": e.code}
        out.append({"name": name, "pinned": pinned, "control_runs": control, "tolerance_ppm": tol, "expect": exp})
    for name, pinned, control, tol, stat in VERIFY_CONTROL_STAT_CASES:
        r = verify_control(pinned, control, tol, stat)
        exp = {
            "ok": r.ok,
            "reasons": list(r.reasons),
            "classes": [
                {"class_id": c.class_id, "pinned_verify_ns": c.pinned_verify_ns, "control_verify_ns": c.control_verify_ns, "drift_ppm": c.drift_ppm, "ok": c.ok}
                for c in r.classes
            ],
        }
        out.append({"name": name, "pinned": pinned, "control_runs": control, "tolerance_ppm": tol, "verify_statistic": stat, "expect": exp})
    vec["verify_control"] = out
    from .calibration import probe_verdict

    out = []
    for name, probes, step, noise, ref in CALIBRATION_PROBE_CASES:
        case = {"name": name, "probes": probes, "max_step_ppm": step, "max_noise_ppm": noise}
        if ref is not None:
            case["reference"] = list(ref)
        try:
            r = probe_verdict(probes, step, noise, ref)
            case["expect"] = {
                "n": r.n, "median_ns": r.median_ns, "noise_ppm": r.noise_ppm, "step_p90_ppm": r.step_p90_ppm,
                "session_drift_ppm": r.session_drift_ppm, "reference_drift_ppm": r.reference_drift_ppm,
                "ok": r.ok, "reasons": list(r.reasons),
            }
        except ValueError:
            case["expect"] = {"error": True}
        out.append(case)
    vec["calibration_probes"] = out
    return vec
