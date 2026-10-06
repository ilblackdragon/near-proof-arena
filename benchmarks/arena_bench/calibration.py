"""Calibration drift checker (docs/BENCHMARK_SPEC.md §6).

A fixed judge calibration workload runs before and after every measurement
session. If the session drifted, or the host no longer matches its governed
reference, the session's results are discarded as INFRA (never charged to the
candidate) and the session is re-run.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Sequence

from .stats import mad_u64, median_u64


@dataclass(frozen=True)
class DriftVerdict:
    ok: bool
    pre_median_ns: int
    post_median_ns: int
    session_drift_ppm: int
    reference_ns: Optional[int]
    reference_drift_ppm: Optional[int]
    pre_mad_ppm: int
    post_mad_ppm: int
    reasons: tuple[str, ...]


def drift_ppm(a: int, b: int) -> int:
    """|b - a| / a in ppm, integer, rounded up (conservative)."""
    if a <= 0:
        raise ValueError("reference must be positive")
    return (abs(b - a) * 1_000_000 + a - 1) // a


def check_drift(
    pre_runs_ns: Sequence[int],
    post_runs_ns: Sequence[int],
    session_threshold_ppm: int = 20_000,
    reference_ns: Optional[int] = None,
    reference_threshold_ppm: int = 50_000,
    max_noise_ppm: int = 20_000,
) -> DriftVerdict:
    """Reasons (any => ok=False => INFRA rerun):
      SESSION_DRIFT     |post - pre| / pre       > session_threshold_ppm
      REFERENCE_DRIFT_PRE / _POST  vs the host's governed reference median
      CALIBRATION_NOISY MAD/median of pre or post > max_noise_ppm
    """
    if not pre_runs_ns or not post_runs_ns:
        raise ValueError("calibration runs missing")
    pre = median_u64(pre_runs_ns)
    post = median_u64(post_runs_ns)
    sd = drift_ppm(pre, post)
    pre_noise = drift_ppm(pre, pre + mad_u64(pre_runs_ns))
    post_noise = drift_ppm(post, post + mad_u64(post_runs_ns))
    reasons = []
    if sd > session_threshold_ppm:
        reasons.append("SESSION_DRIFT")
    rd = None
    if reference_ns is not None:
        rd_pre = drift_ppm(reference_ns, pre)
        rd_post = drift_ppm(reference_ns, post)
        rd = max(rd_pre, rd_post)
        if rd_pre > reference_threshold_ppm:
            reasons.append("REFERENCE_DRIFT_PRE")
        if rd_post > reference_threshold_ppm:
            reasons.append("REFERENCE_DRIFT_POST")
    if pre_noise > max_noise_ppm or post_noise > max_noise_ppm:
        reasons.append("CALIBRATION_NOISY")
    return DriftVerdict(
        ok=not reasons,
        pre_median_ns=pre,
        post_median_ns=post,
        session_drift_ppm=sd,
        reference_ns=reference_ns,
        reference_drift_ppm=rd,
        pre_mad_ppm=pre_noise,
        post_mad_ppm=post_noise,
        reasons=tuple(reasons),
    )


# --- bench-spec-v1.6: in-session probes of the pinned calibration binary -------

PROBE_SMOOTH = 3


@dataclass(frozen=True)
class ProbeVerdict:
    n: int
    median_ns: int
    noise_ppm: int
    step_p90_ppm: int
    session_drift_ppm: int
    reference_drift_ppm: Optional[int]
    ok: bool
    reasons: tuple[str, ...]


def probe_verdict(
    probes: Sequence[int],
    max_step_ppm: int,
    max_noise_ppm: int,
    reference: Optional[tuple[int, int]] = None,
) -> ProbeVerdict:
    """Mirror of `arena_measure::stats::probe_verdict` (BENCHMARK_SPEC §6.1, v1.5).

    Probes in time order (pre, one per measured round, post). Gates:
      CALIBRATION_STEP   order statistic ⌊(m-1)·9/10⌋ of the m sorted consecutive drifts of the
                         rolling medians of PROBE_SMOOTH = 3 probes > max_step_ppm
      CALIBRATION_NOISY  MAD/median of all probes > max_noise_ppm
      REFERENCE_DRIFT    |median - ref| / ref > max_ppm (when a host reference median is pinned)
    Session drift (first vs last probe) is reported, not gated: paired ratios cancel slow drift.
    """
    p = list(probes)
    if len(p) < 2:
        raise ValueError("calibration needs at least 2 probes")
    if any(x == 0 for x in p):
        raise ValueError("calibration probe of 0 ns")
    med = median_u64(p)
    noise = drift_ppm(med, med + mad_u64(p))
    q = [median_u64(p[i:i + PROBE_SMOOTH]) for i in range(len(p) - PROBE_SMOOTH + 1)] if len(p) >= PROBE_SMOOTH else p
    steps = sorted(drift_ppm(a, b) for a, b in zip(q, q[1:])) or [0]
    p90 = steps[(len(steps) - 1) * 9 // 10]
    reasons = []
    if p90 > max_step_ppm:
        reasons.append("CALIBRATION_STEP")
    if noise > max_noise_ppm:
        reasons.append("CALIBRATION_NOISY")
    ref_d = None
    if reference is not None and reference[0] > 0:
        ref_d = drift_ppm(reference[0], med)
        if ref_d > reference[1]:
            reasons.append("REFERENCE_DRIFT")
    return ProbeVerdict(len(p), med, noise, p90, drift_ppm(p[0], p[-1]), ref_d, not reasons, tuple(reasons))
