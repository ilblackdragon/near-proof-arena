"""Reference score function and seeded bootstrap CI (docs/BENCHMARK_SPEC.md §8).

This is the normative reference. `runners/measure` (Rust) must reproduce every
vector in `benchmarks/testvectors/score.json` exactly (integer outputs) and to
within 1e-12 relative error on `score_f64`.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Iterable, Mapping, Sequence

from .stats import SplitMix64, median_u64

PPM = 1_000_000
U64_MAX = (1 << 64) - 1


class ScoreError(ValueError):
    """Score is undefined for this input. `code` is a stable machine id."""

    def __init__(self, code: str, detail: str = ""):
        super().__init__(f"{code}: {detail}" if detail else code)
        self.code = code


@dataclass(frozen=True)
class ClassInput:
    class_id: str
    weight_ppm: int
    baseline_ns: int
    median_ns: int


@dataclass(frozen=True)
class ScoreResult:
    score_f64: float
    score_milli: int


def _is_u(x: object, maxv: int) -> bool:
    return isinstance(x, int) and not isinstance(x, bool) and 0 <= x <= maxv


def _validate(classes: Sequence[ClassInput]) -> list[ClassInput]:
    if not classes:
        raise ScoreError("EMPTY_SUITE")
    seen = set()
    total = 0
    for c in classes:
        if not isinstance(c.class_id, str) or not c.class_id:
            raise ScoreError("BAD_CLASS_ID", repr(c.class_id))
        if c.class_id in seen:
            raise ScoreError("DUPLICATE_CLASS", c.class_id)
        seen.add(c.class_id)
        if not _is_u(c.weight_ppm, 0xFFFF_FFFF):
            raise ScoreError("BAD_WEIGHT", c.class_id)
        if not _is_u(c.baseline_ns, U64_MAX) or c.baseline_ns == 0:
            raise ScoreError("ZERO_OR_BAD_TIME", f"{c.class_id}.baseline_ns")
        if not _is_u(c.median_ns, U64_MAX) or c.median_ns == 0:
            raise ScoreError("ZERO_OR_BAD_TIME", f"{c.class_id}.median_ns")
        total += c.weight_ppm
    if total != PPM:
        raise ScoreError("WEIGHT_SUM", f"weights sum to {total}, expected {PPM}")
    # Canonical summation order: class_id ascending by UTF-8 bytes.
    return sorted(classes, key=lambda c: c.class_id.encode("utf-8"))


def score(classes: Sequence[ClassInput]) -> ScoreResult:
    """score = 100 * exp( (Σ_j w_ppm_j * ln(base_j / cand_j)) / 1e6 ).

    Exact f64 evaluation order (normative):
      acc = 0.0
      for c in classes sorted by class_id bytes:
          r   = f64(c.baseline_ns) / f64(c.median_ns)
          acc = acc + f64(c.weight_ppm) * ln(r)
      s = 100.0 * exp(acc / 1_000_000.0)
      score_milli = floor(s * 1000.0 + 0.5)    (u64; error if not finite or > 2^63)
    """
    ordered = _validate(classes)
    acc = 0.0
    for c in ordered:
        r = float(c.baseline_ns) / float(c.median_ns)
        acc = acc + float(c.weight_ppm) * math.log(r)
    try:
        s = 100.0 * math.exp(acc / 1_000_000.0)
    except OverflowError:
        raise ScoreError("SCORE_OVERFLOW") from None
    m = s * 1000.0 + 0.5
    if not math.isfinite(m) or m >= 2.0**63:
        raise ScoreError("SCORE_OVERFLOW")
    return ScoreResult(score_f64=s, score_milli=int(math.floor(m)))


@dataclass(frozen=True)
class ClassRuns:
    class_id: str
    weight_ppm: int
    baseline_ns: int
    runs_ns: tuple[int, ...]


@dataclass(frozen=True)
class BootstrapResult:
    score_milli: int
    lo_milli: int
    hi_milli: int
    half_width_milli: int
    iterations: int
    seed: int


def score_from_runs(classes: Sequence[ClassRuns]) -> ScoreResult:
    return score(
        [ClassInput(c.class_id, c.weight_ppm, c.baseline_ns, _median_nonempty(c)) for c in classes]
    )


def _median_nonempty(c: ClassRuns) -> int:
    if not c.runs_ns:
        raise ScoreError("NO_RUNS", c.class_id)
    return median_u64(c.runs_ns)


def bootstrap_ci(classes: Sequence[ClassRuns], seed: int, iterations: int = 10_000) -> BootstrapResult:
    """Seeded percentile bootstrap over measured runs (normative algorithm):

      rng = SplitMix64(seed)
      for b in 0..B:
        for c in classes sorted by class_id bytes:
          n = len(c.runs_ns)
          resample = [c.runs_ns[rng.next_u64() % n] for _ in 0..n]
          med_c = median_u64(resample)
        x_b = score(...with med_c...).score_milli
      sort x ascending
      lo = x[((B-1)*25) // 1000]
      hi = x[((B-1)*975 + 999) // 1000]
      half_width = (hi - lo + 1) // 2
    The point estimate is `score_from_runs(classes)`, not the bootstrap mean.
    """
    if iterations < 1:
        raise ValueError("iterations must be >= 1")
    point = score_from_runs(classes)  # also validates
    ordered = sorted(classes, key=lambda c: c.class_id.encode("utf-8"))
    rng = SplitMix64(seed)
    xs: list[int] = []
    for _ in range(iterations):
        inputs = []
        for c in ordered:
            runs = c.runs_ns
            n = len(runs)
            med = median_u64([runs[rng.below(n)] for _ in range(n)])
            inputs.append(ClassInput(c.class_id, c.weight_ppm, c.baseline_ns, med))
        xs.append(score(inputs).score_milli)
    xs.sort()
    b = iterations
    lo = xs[((b - 1) * 25) // 1000]
    hi = xs[((b - 1) * 975 + 999) // 1000]
    return BootstrapResult(
        score_milli=point.score_milli,
        lo_milli=lo,
        hi_milli=hi,
        half_width_milli=(hi - lo + 1) // 2,
        iterations=iterations,
        seed=seed,
    )


def class_inputs_from_json(objs: Iterable[Mapping]) -> list[ClassInput]:
    return [ClassInput(o["class_id"], o["weight_ppm"], o["baseline_ns"], o["median_ns"]) for o in objs]


def class_runs_from_json(objs: Iterable[Mapping]) -> list[ClassRuns]:
    return [ClassRuns(o["class_id"], o["weight_ppm"], o["baseline_ns"], tuple(o["runs_ns"])) for o in objs]
