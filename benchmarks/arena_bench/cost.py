"""Reference cost-normalized score `cost_v1` (docs/BENCHMARK_SPEC.md §14).

Normative reference for `runners/measure/src/cost.rs`; cross-language vectors
in `benchmarks/testvectors/cost.json`. Integer femto-USD arithmetic; the score
is the §8 score with per-class costs in place of times.

Per class, component medians over the measured runs (one run = one batch):
  P = median(prove_runs_ns)  V = median(verify_runs_ns)  S = median(proof_bytes_runs)
  prove_fusd     = ceil(P * vcpus_p * c_cpu / 1e9)
  prepare_fusd   = 0 if A == 0 else ceil(prepare_ns * vcpus_p * c_cpu * batch_size / (1e9 * A))
  verify_fusd    = N_v * ceil(V * vcpus_v * c_cpu / 1e9)
  bandwidth_fusd = N_v * S * c_bw
  storage_fusd   = N_v * S * c_store
  total          = sum (u64; COST_OVERFLOW otherwise; ZERO_COST if 0)
Every intermediate product must fit in u128 (COST_OVERFLOW otherwise), exactly
as the Rust implementation checks it.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Optional, Sequence

from .score import ClassInput, ScoreError, score
from .stats import SplitMix64, lower_quartile_u64, median_u64

VERIFY_STATISTICS = ("median", "lower_quartile")


def verify_stat(stat: str, runs) -> int:
    """V of a class from its per-run verify totals (`scoring.verify_statistic`)."""
    if stat == "median":
        return median_u64(runs)
    if stat == "lower_quartile":
        return lower_quartile_u64(runs)
    raise ValueError(f"verify_statistic {stat!r}")

U64_MAX = (1 << 64) - 1
U128_MAX = (1 << 128) - 1
NS_PER_S = 1_000_000_000


class CostError(ScoreError):
    pass


@dataclass(frozen=True)
class Prices:
    validators_per_chunk: int
    prover_vcpus: int
    verifier_vcpus: int
    cpu_fusd_per_vcpu_second: int
    bandwidth_fusd_per_byte: int
    storage_fusd_per_byte: int
    prepare_amortization_requests: int
    verify_statistic: str = "median"

    @staticmethod
    def from_model(pm: Mapping, prover_vcpus: int, verify_statistic: str = "median") -> "Prices":
        return Prices(
            pm["validators_per_chunk"],
            prover_vcpus,
            pm["verifier_vcpus"],
            pm["cpu_fusd_per_vcpu_second"],
            pm["bandwidth_fusd_per_byte"],
            pm["storage_fusd_per_byte"],
            pm["prepare_amortization_requests"],
            verify_statistic,
        )


@dataclass(frozen=True)
class Components:
    prove_ns: int
    verify_ns: int
    proof_bytes: int


@dataclass(frozen=True)
class Breakdown:
    prove_fusd: int
    prepare_fusd: int
    verify_fusd: int
    bandwidth_fusd: int
    storage_fusd: int
    total_fusd: int


def _mul(a: int, b: int) -> int:
    x = a * b
    if x > U128_MAX:
        raise CostError("COST_OVERFLOW")
    return x


def _ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def _u64(x: int) -> int:
    if x > U64_MAX:
        raise CostError("COST_OVERFLOW")
    return x


def batch_cost(p: Prices, c: Components, prepare_ns: int, batch_size: int) -> Breakdown:
    if p.validators_per_chunk == 0 or p.prover_vcpus == 0 or p.verifier_vcpus == 0 or p.cpu_fusd_per_vcpu_second == 0:
        raise CostError("BAD_PRICES")
    if c.prove_ns == 0 or c.verify_ns == 0:
        raise CostError("ZERO_OR_BAD_TIME")
    cpu, nv = p.cpu_fusd_per_vcpu_second, p.validators_per_chunk
    prove = _ceil_div(_mul(_mul(c.prove_ns, p.prover_vcpus), cpu), NS_PER_S)
    if p.prepare_amortization_requests == 0:
        prepare = 0
    else:
        prepare = _ceil_div(
            _mul(_mul(_mul(prepare_ns, p.prover_vcpus), cpu), batch_size),
            _mul(NS_PER_S, p.prepare_amortization_requests),
        )
    verify_one = _ceil_div(_mul(_mul(c.verify_ns, p.verifier_vcpus), cpu), NS_PER_S)
    verify = _mul(nv, verify_one)
    bandwidth = _mul(nv, _mul(c.proof_bytes, p.bandwidth_fusd_per_byte))
    storage = _mul(nv, _mul(c.proof_bytes, p.storage_fusd_per_byte))
    parts = [_u64(x) for x in (prove, prepare, verify, bandwidth, storage)]
    total = _u64(sum(parts))
    if total == 0:
        raise CostError("ZERO_COST")
    return Breakdown(*parts, total)


@dataclass(frozen=True)
class PairedRuns:
    """bench-spec-v1.6 `baseline_mode = paired`: the reference's per-run totals
    on the same batches (run i paired with candidate run i)."""

    prove_runs_ns: tuple[int, ...]
    verify_runs_ns: tuple[int, ...]
    proof_bytes_runs: tuple[int, ...]


@dataclass(frozen=True)
class CostClassRuns:
    class_id: str
    weight_ppm: int
    batch_size: int
    baseline: Components
    prove_runs_ns: tuple[int, ...]
    verify_runs_ns: tuple[int, ...]
    proof_bytes_runs: tuple[int, ...]
    paired: Optional[PairedRuns] = None


@dataclass(frozen=True)
class CostClassResult:
    class_id: str
    weight_ppm: int
    medians: Components
    cost: Breakdown
    baseline_total_fusd: int
    baseline: Components


@dataclass(frozen=True)
class CostScore:
    score_milli: int
    score_f64: float
    classes: tuple[CostClassResult, ...]
    paired: bool = False


def _check_runs(c: CostClassRuns) -> int:
    n = len(c.prove_runs_ns)
    if n == 0:
        raise CostError("NO_RUNS", c.class_id)
    if len(c.verify_runs_ns) != n or len(c.proof_bytes_runs) != n:
        raise CostError("RUN_LENGTH_MISMATCH", c.class_id)
    r = c.paired
    if r is not None and not (len(r.prove_runs_ns) == len(r.verify_runs_ns) == len(r.proof_bytes_runs) == n):
        raise CostError("RUN_LENGTH_MISMATCH", c.class_id)
    return n


def _stats(p: Prices, prove, verify, bytes_) -> Components:
    return Components(median_u64(prove), verify_stat(p.verify_statistic, verify), median_u64(bytes_))


def _medians(p: Prices, c: CostClassRuns) -> Components:
    return _stats(p, c.prove_runs_ns, c.verify_runs_ns, c.proof_bytes_runs)


def _baseline(p: Prices, c: CostClassRuns) -> Components:
    """Paired runs' statistics (same rules as the candidate's), or the pinned baseline."""
    r = c.paired
    return c.baseline if r is None else _stats(p, r.prove_runs_ns, r.verify_runs_ns, r.proof_bytes_runs)


def cost_score(p: Prices, classes: Sequence[CostClassRuns], prepare_ns: int = 0, baseline_prepare_ns: int = 0) -> CostScore:
    out, inputs = [], []
    for c in classes:
        _check_runs(c)
        m = _medians(p, c)
        cost = batch_cost(p, m, prepare_ns, c.batch_size)
        bc = _baseline(p, c)
        base = batch_cost(p, bc, baseline_prepare_ns, c.batch_size).total_fusd
        inputs.append(ClassInput(c.class_id, c.weight_ppm, base, cost.total_fusd))
        out.append(CostClassResult(c.class_id, c.weight_ppm, m, cost, base, bc))
    s = score(inputs)
    paired = bool(classes) and all(c.paired is not None for c in classes)
    return CostScore(s.score_milli, s.score_f64, tuple(out), paired)


@dataclass(frozen=True)
class CostBootstrap:
    score_milli: int
    lo_milli: int
    hi_milli: int
    half_width_milli: int
    iterations: int
    seed: int


def cost_bootstrap(
    p: Prices,
    classes: Sequence[CostClassRuns],
    prepare_ns: int,
    baseline_prepare_ns: int,
    seed: int,
    iterations: int = 10_000,
) -> CostBootstrap:
    """§8.3 percentile bootstrap; one draw per element resamples the run triple."""
    if iterations < 1:
        raise ValueError("iterations must be >= 1")
    point = cost_score(p, classes, prepare_ns, baseline_prepare_ns)
    ordered = sorted(classes, key=lambda c: c.class_id.encode("utf-8"))
    bases = [batch_cost(p, _baseline(p, c), baseline_prepare_ns, c.batch_size).total_fusd for c in ordered]
    rng = SplitMix64(seed)
    xs = []
    for _ in range(iterations):
        inputs = []
        for c, base in zip(ordered, bases):
            n = len(c.prove_runs_ns)
            idx = [rng.below(n) for _ in range(n)]
            m = Components(
                median_u64([c.prove_runs_ns[i] for i in idx]),
                verify_stat(p.verify_statistic, [c.verify_runs_ns[i] for i in idx]),
                median_u64([c.proof_bytes_runs[i] for i in idx]),
            )
            r = c.paired
            if r is not None:  # the same draw resamples the reference's run i
                rb = _stats(p, [r.prove_runs_ns[i] for i in idx], [r.verify_runs_ns[i] for i in idx], [r.proof_bytes_runs[i] for i in idx])
                base = batch_cost(p, rb, baseline_prepare_ns, c.batch_size).total_fusd
            inputs.append(ClassInput(c.class_id, c.weight_ppm, base, batch_cost(p, m, prepare_ns, c.batch_size).total_fusd))
        xs.append(score(inputs).score_milli)
    xs.sort()
    b = iterations
    lo = xs[((b - 1) * 25) // 1000]
    hi = xs[((b - 1) * 975 + 999) // 1000]
    return CostBootstrap(point.score_milli, lo, hi, (hi - lo + 1) // 2, iterations, seed)


def class_runs_from_json(objs) -> list[CostClassRuns]:
    return [
        CostClassRuns(
            o["class_id"],
            o["weight_ppm"],
            o["batch_size"],
            Components(**o["baseline"]),
            tuple(o["prove_runs_ns"]),
            tuple(o["verify_runs_ns"]),
            tuple(o["proof_bytes_runs"]),
            PairedRuns(tuple(o["paired"]["prove_runs_ns"]), tuple(o["paired"]["verify_runs_ns"]), tuple(o["paired"]["proof_bytes_runs"]))
            if o.get("paired")
            else None,
        )
        for o in objs
    ]


# --- verify drift control (BENCHMARK_SPEC §14.4) -----------------------------

VERIFY_CONTROL_TOLERANCE_PPM = 30_000


@dataclass(frozen=True)
class VerifyControlClass:
    class_id: str
    pinned_verify_ns: int
    control_verify_ns: int
    drift_ppm: int
    ok: bool


@dataclass(frozen=True)
class VerifyControl:
    tolerance_ppm: int
    classes: tuple[VerifyControlClass, ...]
    ok: bool
    reasons: tuple[str, ...]


def verify_control(
    pinned: Mapping[str, int],
    control_runs: Mapping[str, Sequence[int]],
    tolerance_ppm: int = VERIFY_CONTROL_TOLERANCE_PPM,
    stat: str = "median",
) -> VerifyControl:
    """A control session of the reference must reproduce every class's pinned
    verify median (per batch) within `tolerance_ppm`; otherwise VERIFY_DRIFT
    (session infra-invalid). Mirrors `arena_measure::cost::verify_control`."""
    from .calibration import drift_ppm

    if sorted(pinned) != sorted(control_runs):
        raise CostError("MISSING_BASELINE")
    out = []
    for cid in sorted(pinned, key=lambda c: c.encode("utf-8")):
        pin = pinned[cid]
        if pin <= 0:
            raise CostError("ZERO_OR_BAD_TIME")
        runs = list(control_runs[cid])
        if not runs:
            raise CostError("NO_RUNS", cid)
        med = verify_stat(stat, runs)
        d = drift_ppm(pin, med)
        out.append(VerifyControlClass(cid, pin, med, d, d <= tolerance_ppm))
    ok = all(c.ok for c in out)
    return VerifyControl(tolerance_ppm, tuple(out), ok, () if ok else ("VERIFY_DRIFT",))
