import json
from pathlib import Path

import pytest

from arena_bench import testvectors
from arena_bench.cost import Components, CostClassRuns, CostError, Prices, batch_cost, cost_bootstrap, cost_score

VECTORS = Path(__file__).resolve().parent.parent / "testvectors" / "cost.json"

P = Prices(validators_per_chunk=100, prover_vcpus=8, verifier_vcpus=4, cpu_fusd_per_vcpu_second=1_000_000_000,
           bandwidth_fusd_per_byte=10, storage_fusd_per_byte=1, prepare_amortization_requests=0)


def runs(cid, w, base, p, v, s, batch=8):
    return CostClassRuns(cid, w, batch, Components(*base), tuple(p), tuple(v), tuple(s))


def test_hand_breakdown():
    # 1 s prove on 8 vCPUs at 1e9 fUSD/vCPU-s = 8e9; verify 0.5 s on 4 vCPUs = 2e9 per validator.
    b = batch_cost(P, Components(1_000_000_000, 500_000_000, 1_000), 0, 8)
    assert b.prove_fusd == 8_000_000_000
    assert b.verify_fusd == 100 * 2_000_000_000
    assert b.bandwidth_fusd == 100 * 1_000 * 10
    assert b.storage_fusd == 100 * 1_000
    assert b.total_fusd == b.prove_fusd + b.verify_fusd + b.bandwidth_fusd + b.storage_fusd


def test_baseline_scores_100_and_halving_doubles():
    c = runs("a", 1_000_000, (2_000_000_000, 2_000_000_000, 2_000), [2_000_000_000], [2_000_000_000], [2_000])
    assert cost_score(P, [c]).score_milli == 100_000
    h = runs("a", 1_000_000, (2_000_000_000, 2_000_000_000, 2_000), [1_000_000_000], [1_000_000_000], [1_000])
    assert cost_score(P, [h]).score_milli == 200_000


def test_tiny_proof_huge_verify_is_charged_nv_times():
    base = (1_000_000, 1_000_000, 100_000)
    tiny = runs("a", 1_000_000, base, [1_000_000], [100_000_000], [1])  # 100x slower verify, 1-byte proof
    s = cost_score(P, [tiny]).score_milli
    assert s < 100_000


def test_errors():
    with pytest.raises(CostError) as e:
        cost_score(P, [runs("a", 1_000_000, (1, 1, 1), [1], [1, 2], [1])])
    assert e.value.code == "RUN_LENGTH_MISMATCH"
    with pytest.raises(CostError) as e:
        batch_cost(P, Components(1, 0, 0), 0, 1)
    assert e.value.code == "ZERO_OR_BAD_TIME"


def test_bootstrap_order_independent():
    a = runs("a", 500_000, (100, 1000, 50), [90, 95, 120], [900, 1100, 950], [50, 50, 50])
    b = runs("b", 500_000, (200, 5000, 900), [210, 190, 205], [4000, 6000, 4500], [800, 800, 800])
    assert cost_bootstrap(P, [a, b], 0, 0, 3, 100) == cost_bootstrap(P, [b, a], 0, 0, 3, 100)


def test_committed_cost_vectors_are_fresh():
    assert VECTORS.read_text() == testvectors.dumps(testvectors.generate_cost())
    assert json.loads(VECTORS.read_text())["schema"] == "arena-bench-cost-testvectors-v1"


def test_verify_control_vectors_and_rescore_gate():
    """§14.4: the cross-language vectors hold, and an offline re-score refuses a
    cost baseline whose verify control failed unless explicitly labelled."""
    import json
    from pathlib import Path

    import pytest

    from arena_bench import rescore
    from arena_bench.cost import CostError, verify_control

    root = Path(__file__).resolve().parents[2]
    vec = json.loads((root / "benchmarks/testvectors/cost.json").read_text())
    for case in vec["verify_control"]:
        try:
            r = verify_control(case["pinned"], case["control_runs"], case["tolerance_ppm"])
            assert r.ok == case["expect"]["ok"], case["name"]
            assert [c.drift_ppm for c in r.classes] == [c["drift_ppm"] for c in case["expect"]["classes"]]
        except CostError as e:
            assert e.code == case["expect"]["error"], case["name"]

    res = root / "benchmarks/results"
    d = res / "cost-rescore-v1-6-pm-v2-20261006/inputs"
    sub = "sub_c67dd93beafd4ecc9935431366f0baa6"
    args = (
        str(root / "challenges/chl_7c0456cb2d1a36f8601863ac206cfcc9.json"),
        str(root / "challenges/price-models/pm-near-mainnet-2026q4.v2.json"),
        str(res / "baseline-near-transfer-receipt-v1-6-secret-cpus0-7-20261005/session.json"),
        [f"{d / sub}.view.json:{d / sub}.session.json"],
        None,
        str(res / "costbase-near-transfer-receipt-v1-6-secret-cpus0-7-20261006-attempt2-verify-drift/summary.json"),
    )
    with pytest.raises(ValueError, match="verify drift control"):
        rescore.main(*args)
    r = rescore.main(*args, allow_unconfirmed=True)
    assert "UNCONFIRMED" in r["status"] and r["controls"]["confirmed"] is False
