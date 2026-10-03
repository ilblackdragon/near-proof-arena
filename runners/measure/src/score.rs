//! Score function and seeded bootstrap CI — CONTRACTS §7 /
//! docs/BENCHMARK_SPEC.md §8. Pure functions; bit-exact with
//! `benchmarks/arena_bench/score.py` on every integer output.
//!
//! ```text
//! validate: non-empty; ids non-empty & unique; baseline_ns, median_ns > 0;
//!           Σ weight_ppm == 1_000_000
//! order:    class_id ascending by UTF-8 bytes
//! acc = 0.0
//! for c in order: acc += f64(w_ppm) * ln(f64(base) / f64(med))
//! s = 100.0 * exp(acc / 1e6)
//! score_milli = floor(s * 1000.0 + 0.5)  (SCORE_OVERFLOW if !finite or ≥ 2^63)
//! ```

use crate::stats::{median_u64, SplitMix64};
use serde::{Deserialize, Serialize};

pub const PPM: u64 = 1_000_000;
pub const DEFAULT_BOOTSTRAP_ITERATIONS: u32 = 10_000;

/// Stable machine error codes (spec §8.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, thiserror::Error)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum ScoreError {
    #[error("EMPTY_SUITE")]
    EmptySuite,
    #[error("BAD_CLASS_ID")]
    BadClassId,
    #[error("DUPLICATE_CLASS")]
    DuplicateClass,
    #[error("BAD_WEIGHT")]
    BadWeight,
    #[error("ZERO_OR_BAD_TIME")]
    ZeroOrBadTime,
    #[error("WEIGHT_SUM")]
    WeightSum,
    #[error("SCORE_OVERFLOW")]
    ScoreOverflow,
    #[error("NO_RUNS")]
    NoRuns,
}

impl ScoreError {
    pub fn code(self) -> &'static str {
        match self {
            ScoreError::EmptySuite => "EMPTY_SUITE",
            ScoreError::BadClassId => "BAD_CLASS_ID",
            ScoreError::DuplicateClass => "DUPLICATE_CLASS",
            ScoreError::BadWeight => "BAD_WEIGHT",
            ScoreError::ZeroOrBadTime => "ZERO_OR_BAD_TIME",
            ScoreError::WeightSum => "WEIGHT_SUM",
            ScoreError::ScoreOverflow => "SCORE_OVERFLOW",
            ScoreError::NoRuns => "NO_RUNS",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassInput {
    pub class_id: String,
    pub weight_ppm: u32,
    pub baseline_ns: u64,
    pub median_ns: u64,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ScoreResult {
    /// Informative only; never stored in hashed objects.
    pub score_f64: f64,
    pub score_milli: u64,
}

fn score_ordered(ordered: &[(u32, u64, u64)]) -> Result<ScoreResult, ScoreError> {
    let mut acc = 0.0f64;
    for &(w, base, med) in ordered {
        if base == 0 || med == 0 {
            return Err(ScoreError::ZeroOrBadTime);
        }
        let r = base as f64 / med as f64;
        acc += w as f64 * r.ln();
    }
    let s = 100.0 * (acc / 1_000_000.0).exp();
    let m = s * 1000.0 + 0.5;
    if !m.is_finite() || m >= 9_223_372_036_854_775_808.0 {
        return Err(ScoreError::ScoreOverflow);
    }
    Ok(ScoreResult {
        score_f64: s,
        score_milli: m.floor() as u64,
    })
}

/// The score of per-class medians against frozen baselines.
pub fn score(classes: &[ClassInput]) -> Result<ScoreResult, ScoreError> {
    // Same check order as the reference: per class id, duplicate, times;
    // then the weight sum. (`weight_ppm: u32` makes BAD_WEIGHT unrepresentable.)
    if classes.is_empty() {
        return Err(ScoreError::EmptySuite);
    }
    let mut seen = std::collections::BTreeSet::new();
    for c in classes {
        if c.class_id.is_empty() {
            return Err(ScoreError::BadClassId);
        }
        if !seen.insert(c.class_id.as_bytes()) {
            return Err(ScoreError::DuplicateClass);
        }
        if c.baseline_ns == 0 || c.median_ns == 0 {
            return Err(ScoreError::ZeroOrBadTime);
        }
    }
    if classes.iter().map(|c| c.weight_ppm as u64).sum::<u64>() != PPM {
        return Err(ScoreError::WeightSum);
    }
    let mut ordered: Vec<&ClassInput> = classes.iter().collect();
    ordered.sort_by(|a, b| a.class_id.as_bytes().cmp(b.class_id.as_bytes()));
    let v: Vec<(u32, u64, u64)> = ordered
        .iter()
        .map(|c| (c.weight_ppm, c.baseline_ns, c.median_ns))
        .collect();
    score_ordered(&v)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassRuns {
    pub class_id: String,
    pub weight_ppm: u32,
    pub baseline_ns: u64,
    pub runs_ns: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BootstrapResult {
    /// Point estimate: score of the actual medians.
    pub score_milli: u64,
    pub lo_milli: u64,
    pub hi_milli: u64,
    /// `(hi - lo + 1) / 2` — `BenchmarkResult.score_ci_milli`.
    pub half_width_milli: u64,
    pub iterations: u32,
    pub seed: u64,
}

fn to_inputs(classes: &[ClassRuns]) -> Result<Vec<ClassInput>, ScoreError> {
    classes
        .iter()
        .map(|c| {
            Ok(ClassInput {
                class_id: c.class_id.clone(),
                weight_ppm: c.weight_ppm,
                baseline_ns: c.baseline_ns,
                median_ns: median_u64(&c.runs_ns).ok_or(ScoreError::NoRuns)?,
            })
        })
        .collect()
}

pub fn score_from_runs(classes: &[ClassRuns]) -> Result<ScoreResult, ScoreError> {
    score(&to_inputs(classes)?)
}

/// Seeded percentile bootstrap (§8.3).
pub fn bootstrap_ci(
    classes: &[ClassRuns],
    seed: u64,
    iterations: u32,
) -> Result<BootstrapResult, ScoreError> {
    assert!(iterations >= 1, "iterations must be >= 1");
    let point = score_from_runs(classes)?;
    let mut ordered: Vec<&ClassRuns> = classes.iter().collect();
    ordered.sort_by(|a, b| a.class_id.as_bytes().cmp(b.class_id.as_bytes()));
    let mut rng = SplitMix64::new(seed);
    let mut xs: Vec<u64> = Vec::with_capacity(iterations as usize);
    let mut buf = Vec::new();
    let mut tuples = Vec::with_capacity(ordered.len());
    for _ in 0..iterations {
        tuples.clear();
        for c in &ordered {
            let n = c.runs_ns.len() as u64;
            buf.clear();
            for _ in 0..n {
                buf.push(c.runs_ns[rng.below(n) as usize]);
            }
            tuples.push((
                c.weight_ppm,
                c.baseline_ns,
                median_u64(&buf).expect("non-empty"),
            ));
        }
        xs.push(score_ordered(&tuples)?.score_milli);
    }
    xs.sort_unstable();
    let b = iterations as usize;
    let lo = xs[((b - 1) * 25) / 1000];
    let hi = xs[((b - 1) * 975).div_ceil(1000)];
    Ok(BootstrapResult {
        score_milli: point.score_milli,
        lo_milli: lo,
        hi_milli: hi,
        half_width_milli: (hi - lo).div_ceil(2),
        iterations,
        seed,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn c(id: &str, w: u32, b: u64, m: u64) -> ClassInput {
        ClassInput {
            class_id: id.into(),
            weight_ppm: w,
            baseline_ns: b,
            median_ns: m,
        }
    }
    #[test]
    fn basics() {
        assert_eq!(
            score(&[c("a", 1_000_000, 10, 10)]).unwrap().score_milli,
            100_000
        );
        assert_eq!(
            score(&[c("a", 500_000, 2, 1), c("b", 500_000, 8, 4)])
                .unwrap()
                .score_milli,
            200_000
        );
        assert_eq!(score(&[]).unwrap_err(), ScoreError::EmptySuite);
        assert_eq!(
            score(&[c("a", 1, 1, 1)]).unwrap_err(),
            ScoreError::WeightSum
        );
        assert_eq!(
            score(&[c("a", 1_000_000, 1, 0)]).unwrap_err(),
            ScoreError::ZeroOrBadTime
        );
        assert_eq!(
            score(&[c("", 1_000_000, 1, 1)]).unwrap_err(),
            ScoreError::BadClassId
        );
        assert_eq!(
            score(&[c("a", 1_000_000, u64::MAX, 1)]).unwrap_err(),
            ScoreError::ScoreOverflow
        );
    }
    #[test]
    fn order_independent() {
        let a = [c("x", 300_000, 1000, 700), c("y", 700_000, 5000, 6100)];
        let b = [a[1].clone(), a[0].clone()];
        assert_eq!(
            score(&a).unwrap().score_milli,
            score(&b).unwrap().score_milli
        );
    }
    #[test]
    fn half_width_rounds_up() {
        assert_eq!(3u64.div_ceil(2), 2);
    }

    use proptest::prelude::*;
    proptest! {
        #[test]
        fn prop_identity_and_permutation(ws in prop::collection::vec(1u32..1000, 1..6), ts in prop::collection::vec(1u64..1u64 << 40, 6), seed in any::<u64>()) {
            let total: u32 = ws.iter().sum();
            let mut weights: Vec<u32> = ws.iter().map(|w| (*w as u64 * 1_000_000 / total as u64) as u32).collect();
            let fix = 1_000_000 - weights.iter().sum::<u32>();
            weights[0] += fix;
            let same: Vec<ClassInput> = weights.iter().enumerate().map(|(i, &w)| c(&format!("c{i}"), w, ts[i], ts[i])).collect();
            prop_assert_eq!(score(&same).unwrap().score_milli, 100_000);
            let mut runs: Vec<ClassRuns> = weights.iter().enumerate().map(|(i, &w)| ClassRuns { class_id: format!("c{i}"), weight_ppm: w, baseline_ns: ts[i], runs_ns: vec![ts[i], ts[i] / 2 + 1, ts[i] * 2] }).collect();
            let a = bootstrap_ci(&runs, seed, 50).unwrap();
            runs.reverse();
            let b = bootstrap_ci(&runs, seed, 50).unwrap();
            prop_assert_eq!(&a, &b);
            prop_assert!(a.lo_milli <= a.hi_milli);
        }
    }
}
