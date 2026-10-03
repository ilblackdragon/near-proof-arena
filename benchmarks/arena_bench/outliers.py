"""Outlier flagging (docs/BENCHMARK_SPEC.md §7.3). Flags, never drops."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Sequence

from .stats import mad_u64, median_u64


@dataclass(frozen=True)
class OutlierReport:
    median_ns: int
    mad_ns: int
    k: int
    flagged_indices: tuple[int, ...]
    # Fraction of runs flagged, ppm (integer, floor).
    flagged_ppm: int
    # True when flagged_ppm exceeds the session limit -> infra rerun of the class.
    excessive: bool
    notes: tuple[str, ...] = field(default=())


def flag_outliers(runs_ns: Sequence[int], k: int, max_flagged_ppm: int = 200_000) -> OutlierReport:
    """Flag run i iff |x_i - median| > k * MAD (integer arithmetic, strict >).

    When MAD == 0 the rule degenerates to "any deviation from the median",
    which on real hardware almost never happens for >= 5 runs; it is reported
    with a note instead of being special-cased away.
    All runs (flagged or not) remain in the median, MAD and bootstrap.
    """
    if not runs_ns:
        raise ValueError("no runs")
    if k < 1:
        raise ValueError("k must be >= 1")
    med = median_u64(runs_ns)
    mad = mad_u64(runs_ns)
    flagged = tuple(i for i, x in enumerate(runs_ns) if abs(x - med) > k * mad)
    ppm = len(flagged) * 1_000_000 // len(runs_ns)
    notes = ("MAD_ZERO",) if mad == 0 else ()
    return OutlierReport(
        median_ns=med,
        mad_ns=mad,
        k=k,
        flagged_indices=flagged,
        flagged_ppm=ppm,
        excessive=ppm > max_flagged_ppm,
        notes=notes,
    )


@dataclass(frozen=True)
class TripwireResult:
    suspected: bool
    measured_median_ns: int
    fresh_median_ns: int
    slowdown_ppm: int


def caching_tripwire(
    measured_runs_ns: Sequence[int],
    fresh_runs_ns: Sequence[int],
    k: int,
    min_slowdown_ppm: int = 50_000,
) -> TripwireResult:
    """Cross-run caching tripwire (§7.4, §12).

    The `fresh_confirm` phase proves a batch the candidate has never seen in
    this session. If it is slower than the steady-state median by more than
    BOTH k * MAD and `min_slowdown_ppm`, steady-state numbers may have been
    helped by state that survived between runs: CACHING_SUSPECTED, the
    submission goes to manual review / re-run with fresh batches only.
    """
    if not measured_runs_ns or not fresh_runs_ns:
        raise ValueError("runs missing")
    med = median_u64(measured_runs_ns)
    mad = mad_u64(measured_runs_ns)
    fresh = median_u64(fresh_runs_ns)
    delta = fresh - med
    slowdown_ppm = max(0, delta) * 1_000_000 // med if med else 0
    suspected = delta > k * mad and slowdown_ppm > min_slowdown_ppm
    return TripwireResult(suspected, med, fresh, slowdown_ppm)
