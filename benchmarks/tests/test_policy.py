import json
from collections import Counter

import pytest

from arena_bench.calibration import check_drift, drift_ppm
from arena_bench.outliers import caching_tripwire, flag_outliers
from arena_bench.schedule import build_schedule, shuffle
from arena_bench.seeds import commit_secret, derive_sampling_seed, derive_seed, verify_reveal
from arena_bench.stats import SplitMix64


# ---- outliers ----

def test_outliers_flag_not_drop():
    runs = [1_000, 1_010, 990, 1_005, 995, 1_500, 600]
    o = flag_outliers(runs, k=3)
    assert (o.median_ns, o.mad_ns) == (1_000, 10)
    assert o.flagged_indices == (5, 6)
    assert o.flagged_ppm == 2 * 1_000_000 // 7
    assert o.excessive  # 28.6% > 20%


def test_outliers_boundary_is_strict():
    # median 100, MAD 10: |x-100| == 30 is NOT flagged at k=3, 31 is.
    o = flag_outliers([90, 100, 110, 100, 130], k=3)
    assert (o.median_ns, o.mad_ns, o.flagged_indices) == (100, 10, ())
    assert flag_outliers([90, 100, 110, 100, 131], k=3).flagged_indices == (4,)
    assert flag_outliers([100, 100, 100, 100, 101], k=5).notes == ("MAD_ZERO",)


def test_caching_tripwire():
    steady = [1_000, 1_010, 990, 1_005, 995]
    assert not caching_tripwire(steady, [1_020], k=3).suspected
    t = caching_tripwire(steady, [1_400], k=3)
    assert t.suspected and t.slowdown_ppm == 400_000
    # big relative gap but within k*MAD of a very noisy class -> not suspected
    assert not caching_tripwire([500, 1_000, 1_500, 1_000, 900], [1_200], k=3).suspected


# ---- calibration ----

def test_drift_ppm_rounds_up():
    assert drift_ppm(1_000, 1_020) == 20_000
    assert drift_ppm(3, 4) == 333_334


def test_calibration_ok_and_fail():
    pre = [1_000_000, 1_001_000, 999_000, 1_000_500, 1_000_000]
    assert check_drift(pre, pre).ok
    v = check_drift(pre, [x * 103 // 100 for x in pre])
    assert not v.ok and "SESSION_DRIFT" in v.reasons
    v = check_drift(pre, pre, reference_ns=1_100_000)
    assert not v.ok and {"REFERENCE_DRIFT_PRE", "REFERENCE_DRIFT_POST"} <= set(v.reasons)
    noisy = [1_000_000, 1_200_000, 800_000, 1_150_000, 850_000]
    assert "CALIBRATION_NOISY" in check_drift(noisy, noisy).reasons


# ---- schedule ----

def test_shuffle_is_permutation_and_seeded():
    items = [str(i) for i in range(20)]
    a = shuffle(items, SplitMix64(5))
    assert sorted(a) == sorted(items) and a != items
    assert a == shuffle(items, SplitMix64(5))
    assert a != shuffle(items, SplitMix64(6))


def test_schedule_layout():
    s = build_schedule(["c", "a", "b"], seed=7, cold_runs=1, warmup_runs=2, measured_runs=5, fresh_confirm_runs=1, calibration_runs=3)
    phases = [e.phase for e in s]
    # phase blocks are contiguous and ordered
    order = []
    for p in phases:
        if not order or order[-1] != p:
            order.append(p)
    assert order == ["calibration_pre", "cold", "warmup", "measured", "fresh_confirm", "calibration_post"]
    cnt = Counter((e.phase, e.class_id) for e in s)
    assert cnt[("measured", "a")] == 5 and cnt[("warmup", "b")] == 2 and cnt[("calibration_pre", "")] == 3
    assert [e.seq for e in s] == list(range(len(s)))
    # every round is a full permutation
    for r in range(5):
        assert sorted(e.class_id for e in s if e.phase == "measured" and e.round == r) == ["a", "b", "c"]
    # input order does not matter, seed does
    assert s == build_schedule(["b", "c", "a"], 7, 1, 2, 5, 1, 3)
    assert s != build_schedule(["a", "b", "c"], 8, 1, 2, 5, 1, 3)


def test_schedule_rejects_duplicates():
    with pytest.raises(ValueError):
        build_schedule(["a", "a"], 1, 0, 0, 1)


# ---- seeds ----

def test_derive_seed_is_documented_construction():
    import hashlib

    want = int.from_bytes(hashlib.sha256(b"near-arena-seed-v1|schedule|chl_x|sub_y").digest()[:8], "big")
    assert derive_seed("schedule", "chl_x", "sub_y") == want
    with pytest.raises(ValueError):
        derive_seed("a|b")


def test_commit_reveal_and_sampling_seed():
    secret = bytes(range(32))
    c = commit_secret(secret)
    assert verify_reveal(secret, c)
    assert not verify_reveal(bytes(32), c)
    s1 = derive_sampling_seed(secret, "chl_ab", "sha256:" + "00" * 32, "transfer")
    s2 = derive_sampling_seed(secret, "chl_ab", "sha256:" + "01" * 32, "transfer")
    s3 = derive_sampling_seed(secret, "chl_ab", "sha256:" + "00" * 32, "other")
    assert len({s1, s2, s3}) == 3
    with pytest.raises(ValueError):
        commit_secret(b"short")


# ---- CLI smoke ----

def test_cli_score_and_schedule(tmp_path, capsys):
    from arena_bench.__main__ import main

    p = tmp_path / "c.json"
    p.write_text(json.dumps([{"class_id": "a", "weight_ppm": 1_000_000, "baseline_ns": 2, "median_ns": 1}]))
    assert main(["score", "--input", str(p)]) == 0
    assert json.loads(capsys.readouterr().out)["score_milli"] == 200_000
    p.write_text(json.dumps([{"class_id": "a", "weight_ppm": 1, "baseline_ns": 2, "median_ns": 1}]))
    assert main(["score", "--input", str(p)]) == 2
    assert json.loads(capsys.readouterr().out)["error"] == "WEIGHT_SUM"
    assert main(["drift", "--pre", "100,100,100", "--post", "110,110,110"]) == 3
    capsys.readouterr()
    assert main(["gen-testvectors", "--check"]) == 0
