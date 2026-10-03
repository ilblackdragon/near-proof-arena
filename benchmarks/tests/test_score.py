import json
import math
from pathlib import Path

import pytest

from arena_bench import testvectors
from arena_bench.score import ClassInput, ClassRuns, ScoreError, bootstrap_ci, score, score_from_runs
from arena_bench.stats import SplitMix64, mad_u64, median_u64

VECTORS = Path(__file__).resolve().parent.parent / "testvectors" / "score.json"


def ci(cid, w, b, m):
    return ClassInput(cid, w, b, m)


# ---- hand-derived values (independent of the committed vectors) ----

def test_splitmix64_reference_value():
    # Published reference: SplitMix64 seeded with 0 yields 0xE220A8397B1DCDAF first.
    assert SplitMix64(0).next_u64() == 0xE220A8397B1DCDAF


def test_median_mad():
    assert median_u64([3, 1]) == 2
    assert median_u64([1, 2]) == 1  # floor
    assert median_u64([5, 1, 9]) == 5
    assert mad_u64([1, 2, 3, 4, 100]) == 1
    big = (1 << 64) - 1
    assert median_u64([big, big - 2]) == big - 1
    with pytest.raises(ValueError):
        median_u64([])
    with pytest.raises(ValueError):
        median_u64([-1])


@pytest.mark.parametrize(
    "classes,expect_milli",
    [
        ([ci("a", 1_000_000, 10, 10)], 100_000),
        ([ci("a", 500_000, 2, 1), ci("b", 500_000, 4, 2)], 200_000),
        ([ci("a", 500_000, 2, 1), ci("b", 500_000, 1, 2)], 100_000),
        ([ci("a", 1_000_000, 1, 3)], 33_333),
        ([ci("a", 250_000, 16, 1), ci("b", 750_000, 1, 1)], 200_000),  # 16^0.25 = 2
    ],
)
def test_score_hand_values(classes, expect_milli):
    assert score(classes).score_milli == expect_milli


def test_score_matches_weighted_geometric_mean():
    cs = [ci("x", 123_456, 9_999, 3_333), ci("y", 876_544, 5_000, 7_000)]
    geo = 100 * math.prod((c.baseline_ns / c.median_ns) ** (c.weight_ppm / 1e6) for c in cs)
    assert math.isclose(score(cs).score_f64, geo, rel_tol=1e-12)


def test_score_order_independent_and_monotone():
    cs = [ci("b", 400_000, 100, 90), ci("a", 600_000, 100, 120)]
    assert score(cs) == score(list(reversed(cs)))
    faster = [ci("b", 400_000, 100, 80), ci("a", 600_000, 100, 120)]
    assert score(faster).score_milli > score(cs).score_milli


@pytest.mark.parametrize(
    "classes,code",
    [
        ([], "EMPTY_SUITE"),
        ([ci("a", 999_999, 1, 1)], "WEIGHT_SUM"),
        ([ci("a", 1_000_000, 1, 0)], "ZERO_OR_BAD_TIME"),
        ([ci("a", 1_000_000, 0, 1)], "ZERO_OR_BAD_TIME"),
        ([ci("a", 500_000, 1, 1), ci("a", 500_000, 1, 1)], "DUPLICATE_CLASS"),
        ([ci("a", 1_000_000, (1 << 64) - 1, 1)], "SCORE_OVERFLOW"),
        ([ci("a", 1_000_000, 1.5, 1)], "ZERO_OR_BAD_TIME"),
        ([ci("a", 1_000_000, True, 1)], "ZERO_OR_BAD_TIME"),
    ],
)
def test_score_errors(classes, code):
    with pytest.raises(ScoreError) as e:
        score(classes)
    assert e.value.code == code


def test_bootstrap_constant_runs_zero_width():
    r = bootstrap_ci([ClassRuns("a", 1_000_000, 1_000, (500,) * 7)], seed=9, iterations=100)
    assert (r.score_milli, r.lo_milli, r.hi_milli, r.half_width_milli) == (200_000, 200_000, 200_000, 0)


def test_bootstrap_deterministic_and_seed_sensitive():
    cs = [ClassRuns("a", 1_000_000, 1_000, (480, 500, 510, 530, 470, 505, 650))]
    a = bootstrap_ci(cs, seed=1, iterations=300)
    b = bootstrap_ci(cs, seed=1, iterations=300)
    c = bootstrap_ci(cs, seed=2, iterations=300)
    assert a == b
    assert a.lo_milli <= a.score_milli <= a.hi_milli
    # Few runs -> few distinct resample medians; seed sensitivity needs richer data.
    wide = [ClassRuns("a", 1_000_000, 100_000, tuple(1_000 + (i * 7919) % 613 for i in range(41)))]
    assert bootstrap_ci(wide, 1, 300) != bootstrap_ci(wide, 2, 300)
    assert a.score_milli == score_from_runs(cs).score_milli


def test_bootstrap_no_runs():
    with pytest.raises(ScoreError) as e:
        bootstrap_ci([ClassRuns("a", 1_000_000, 1, ())], seed=1, iterations=10)
    assert e.value.code == "NO_RUNS"


# ---- committed cross-language vectors ----

def test_vectors_file_is_fresh():
    assert VECTORS.read_text() == testvectors.dumps(testvectors.generate())


def test_vectors_contain_no_json_floats():
    def walk(x):
        if isinstance(x, float):
            raise AssertionError(f"float in vectors: {x}")
        if isinstance(x, dict):
            for v in x.values():
                walk(v)
        if isinstance(x, list):
            for v in x:
                walk(v)

    walk(json.loads(VECTORS.read_text()))


def test_vectors_replay():
    v = json.loads(VECTORS.read_text())
    tol = float(v["score_f64_rel_tolerance"])
    for case in v["score"]:
        exp = case["expect"]
        inputs = [ClassInput(**c) for c in case["classes"]]
        if "error" in exp:
            with pytest.raises(ScoreError) as e:
                score(inputs)
            assert e.value.code == exp["error"], case["name"]
        else:
            r = score(inputs)
            assert r.score_milli == exp["score_milli"], case["name"]
            assert math.isclose(r.score_f64, float(exp["score_f64"]), rel_tol=tol)
    for case in v["bootstrap"]:
        runs = [ClassRuns(c["class_id"], c["weight_ppm"], c["baseline_ns"], tuple(c["runs_ns"])) for c in case["classes"]]
        if "error" in case["expect"]:
            with pytest.raises(ScoreError):
                bootstrap_ci(runs, case["seed"], case["iterations"])
            continue
        r = bootstrap_ci(runs, case["seed"], case["iterations"])
        assert {k: getattr(r, k) for k in case["expect"]} == case["expect"], case["name"]
    for case in v["splitmix64"]:
        g = SplitMix64(case["seed"])
        assert [g.next_u64() for _ in case["outputs"]] == case["outputs"]
    for case in v["median_mad"]:
        assert (median_u64(case["input"]), mad_u64(case["input"])) == (case["median"], case["mad"])


def test_vectors_hand_anchors():
    """The committed file must agree with hand-derived values."""
    v = json.loads(VECTORS.read_text())
    by = {c["name"]: c["expect"] for c in v["score"]}
    assert by["identity"]["score_milli"] == 100_000
    assert by["uniform_2x_faster"]["score_milli"] == 200_000
    assert by["opposite_cancel"]["score_milli"] == 100_000
    assert by["single_3x_slower"]["score_milli"] == 33_333
    assert by["three_class_realistic"] == by["three_class_realistic_permuted"]
    assert by["zero_weight_class_ignored"]["score_milli"] == 125_000
    assert by["1000x_speedup"]["score_milli"] == 100_000_000
    assert v["splitmix64"][0]["outputs"][0] == 0xE220A8397B1DCDAF
