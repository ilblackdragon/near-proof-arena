//! Server-side score computation (CONTRACTS §7). Scores reported by workers are
//! never trusted; the control plane recomputes them from judge measurements and
//! the challenge's frozen weights and baselines.

use arena_types::{BenchmarkResult, ChallengeDefinition};
use std::collections::HashMap;

/// Validate the benchmark against the challenge's workload suite and fill in
/// the challenge baselines. Returns an error for protocol violations
/// (unknown/missing classes, mismatched weights, zero medians).
pub fn normalize_benchmark(
    chal: &ChallengeDefinition,
    mut b: BenchmarkResult,
) -> Result<BenchmarkResult, String> {
    let suite = &chal.workload_suite;
    if b.suite_revision != suite.revision {
        return Err(format!(
            "benchmark suite revision {:?} != challenge suite revision {:?}",
            b.suite_revision, suite.revision
        ));
    }
    let weights: HashMap<&str, u32> =
        suite.classes.iter().map(|c| (c.id.as_str(), c.weight_ppm)).collect();
    if b.classes.len() != weights.len() {
        return Err(format!(
            "benchmark has {} classes, challenge defines {}",
            b.classes.len(),
            weights.len()
        ));
    }
    let baselines: HashMap<&str, u64> =
        suite.baseline_ns.iter().map(|(k, v)| (k.as_str(), *v)).collect();
    let mut seen = std::collections::HashSet::new();
    for c in &mut b.classes {
        let Some(w) = weights.get(c.class_id.as_str()) else {
            return Err(format!("unknown workload class {:?}", c.class_id));
        };
        if !seen.insert(c.class_id.clone()) {
            return Err(format!("duplicate workload class {:?}", c.class_id));
        }
        if c.weight_ppm != *w {
            return Err(format!("class {:?} weight {} != challenge weight {}", c.class_id, c.weight_ppm, w));
        }
        if c.median_ns == 0 {
            return Err(format!("class {:?} has zero median", c.class_id));
        }
        c.baseline_ns = baselines.get(c.class_id.as_str()).copied().unwrap_or(0);
    }
    b.score_milli = compute_score_milli(&b);
    b.hardware_profile = arena_jobs::sanitize::sanitize_line(&b.hardware_profile, 128);
    b.measured_by = arena_jobs::sanitize::sanitize_line(&b.measured_by, 128);
    Ok(b)
}

/// `100 * exp(Σ_j w_j * ln(T_base_j / T_cand_j))`, in milli-units. `None` if any
/// baseline is missing/zero or the result is not finite.
pub fn compute_score_milli(b: &BenchmarkResult) -> Option<u64> {
    if b.classes.is_empty() {
        return None;
    }
    let mut acc = 0f64;
    let mut wsum = 0u64;
    for c in &b.classes {
        if c.baseline_ns == 0 || c.median_ns == 0 {
            return None;
        }
        acc += (c.weight_ppm as f64 / 1e6) * ((c.baseline_ns as f64) / (c.median_ns as f64)).ln();
        wsum += c.weight_ppm as u64;
    }
    if wsum != 1_000_000 {
        return None;
    }
    let score = 100.0 * acc.exp();
    if !score.is_finite() || score < 0.0 || score * 1000.0 > u64::MAX as f64 / 2.0 {
        return None;
    }
    Some((score * 1000.0).round() as u64)
}

#[cfg(test)]
mod tests {
    use super::*;
    use arena_types::ClassMeasurement;
    fn cm(id: &str, w: u32, med: u64, base: u64) -> ClassMeasurement {
        ClassMeasurement {
            class_id: id.into(),
            weight_ppm: w,
            runs_ns: vec![med],
            median_ns: med,
            mad_ns: 0,
            cold_ns: None,
            baseline_ns: base,
            verify_median_ns: 1,
            proof_bytes_max: 1,
            peak_rss_bytes: 1,
        }
    }
    fn br(classes: Vec<ClassMeasurement>) -> BenchmarkResult {
        BenchmarkResult {
            hardware_profile: "hw".into(),
            suite_revision: "r1".into(),
            classes,
            score_milli: Some(999_999_999),
            score_ci_milli: None,
            prepare_ns: 0,
            public_artifact_bytes: 0,
            measured_by: "judge".into(),
        }
    }
    #[test]
    fn baseline_equals_100() {
        assert_eq!(compute_score_milli(&br(vec![cm("a", 1_000_000, 50, 50)])), Some(100_000));
    }
    #[test]
    fn twice_as_fast_is_200() {
        let b = br(vec![cm("a", 500_000, 50, 100), cm("b", 500_000, 25, 50)]);
        assert_eq!(compute_score_milli(&b), Some(200_000));
    }
    #[test]
    fn geometric_weighting() {
        // 4x faster on half the weight, same on the other half -> 100*sqrt(4) = 200
        let b = br(vec![cm("a", 500_000, 25, 100), cm("b", 500_000, 50, 50)]);
        assert_eq!(compute_score_milli(&b), Some(200_000));
    }
    #[test]
    fn missing_baseline_no_score() {
        assert_eq!(compute_score_milli(&br(vec![cm("a", 1_000_000, 50, 0)])), None);
    }
}
