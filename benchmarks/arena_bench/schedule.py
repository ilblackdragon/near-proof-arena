"""Seeded, recorded run-order randomization (docs/BENCHMARK_SPEC.md §5)."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Sequence

from .stats import SplitMix64

PHASES = ("calibration_pre", "cold", "warmup", "measured", "fresh_confirm", "calibration_post")


@dataclass(frozen=True)
class ScheduledRun:
    seq: int
    phase: str
    class_id: str  # "" for calibration entries
    round: int

    def to_json(self) -> dict:
        return asdict(self)


def shuffle(items: Sequence[str], rng: SplitMix64) -> list[str]:
    """Fisher-Yates, i from n-1 down to 1, j = rng.below(i + 1)."""
    out = list(items)
    for i in range(len(out) - 1, 0, -1):
        j = rng.below(i + 1)
        out[i], out[j] = out[j], out[i]
    return out


def build_schedule(
    class_ids: Sequence[str],
    seed: int,
    cold_runs: int,
    warmup_runs: int,
    measured_runs: int,
    fresh_confirm_runs: int = 1,
    calibration_runs: int = 5,
) -> list[ScheduledRun]:
    """Session layout (concurrency 1, strictly sequential):

      calibration_pre  x calibration_runs
      cold             cold_runs rounds        (each run: fresh VM, dropped caches)
      warmup           warmup_runs rounds      (unscored)
      measured         measured_runs rounds    (scored; steady state)
      fresh_confirm    fresh_confirm_runs rounds (unseen batch; caching tripwire)
      calibration_post x calibration_runs

    Every round of a non-calibration phase is an independent Fisher-Yates
    permutation of the class ids (sorted by UTF-8 bytes first), drawn from a
    single SplitMix64(seed) stream in schedule order. The seed and the full
    schedule are recorded in the benchmark report.
    """
    if len(set(class_ids)) != len(class_ids) or not class_ids:
        raise ValueError("class ids must be non-empty and unique")
    base = sorted(class_ids, key=lambda s: s.encode("utf-8"))
    rng = SplitMix64(seed)
    out: list[ScheduledRun] = []

    def emit(phase: str, cid: str, rnd: int) -> None:
        out.append(ScheduledRun(seq=len(out), phase=phase, class_id=cid, round=rnd))

    for r in range(calibration_runs):
        emit("calibration_pre", "", r)
    for phase, rounds in (
        ("cold", cold_runs),
        ("warmup", warmup_runs),
        ("measured", measured_runs),
        ("fresh_confirm", fresh_confirm_runs),
    ):
        for r in range(rounds):
            for cid in shuffle(base, rng):
                emit(phase, cid, r)
    for r in range(calibration_runs):
        emit("calibration_post", "", r)
    return out
