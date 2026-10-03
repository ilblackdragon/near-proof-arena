"""NEAR Proof Arena benchmark policy reference implementation (stdlib only).

Normative spec: docs/BENCHMARK_SPEC.md. The measurement *mechanism* lives in
`runners/measure` (Rust); this package is the reference for the policy math
(score, CI, outliers, calibration, run order, seeds) and its test vectors.
"""

from .score import ClassInput, ClassRuns, ScoreError, bootstrap_ci, score, score_from_runs
from .stats import SplitMix64, mad_u64, median_u64

__all__ = [
    "ClassInput",
    "ClassRuns",
    "ScoreError",
    "SplitMix64",
    "bootstrap_ci",
    "mad_u64",
    "median_u64",
    "score",
    "score_from_runs",
]
