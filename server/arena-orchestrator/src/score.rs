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
    let weights: HashMap<&str, u32> = suite
        .classes
        .iter()
        .map(|c| (c.id.as_str(), c.weight_ppm))
        .collect();
    if b.classes.len() != weights.len() {
        return Err(format!(
            "benchmark has {} classes, challenge defines {}",
            b.classes.len(),
            weights.len()
        ));
    }
    let baselines: HashMap<&str, u64> = suite
        .baseline_ns
        .iter()
        .map(|(k, v)| (k.as_str(), *v))
        .collect();
    let mut seen = std::collections::HashSet::new();
    for c in &mut b.classes {
        let Some(w) = weights.get(c.class_id.as_str()) else {
            return Err(format!("unknown workload class {:?}", c.class_id));
        };
        if !seen.insert(c.class_id.clone()) {
            return Err(format!("duplicate workload class {:?}", c.class_id));
        }
        if c.weight_ppm != *w {
            return Err(format!(
                "class {:?} weight {} != challenge weight {}",
                c.class_id, c.weight_ppm, w
            ));
        }
        if c.median_ns == 0 {
            return Err(format!("class {:?} has zero median", c.class_id));
        }
        c.baseline_ns = baselines.get(c.class_id.as_str()).copied().unwrap_or(0);
    }
    b.score_milli = compute_score_milli(&b);
    b.cost = compute_cost(chal, &b);
    b.hardware_profile = arena_jobs::sanitize::sanitize_line(&b.hardware_profile, 128);
    b.measured_by = arena_jobs::sanitize::sanitize_line(&b.measured_by, 128);
    Ok(b)
}

/// The cost-board result (docs/BENCHMARK_SPEC.md §14), recomputed from the
/// judge's per-run measurements and the challenge's pinned price model and
/// reference costs. `None` for speed-only challenges (whatever the worker
/// sent: scores of different kinds are never mixed) and when the per-run
/// verify/bytes vectors are missing or inconsistent. The worker's bootstrap
/// half-width is kept (as for the speed score).
pub fn compute_cost(
    chal: &ChallengeDefinition,
    b: &BenchmarkResult,
) -> Option<arena_types::CostResult> {
    let sc = chal.scoring.as_ref()?;
    if sc.kind != arena_types::ScoringKind::CostV1 || chal.check_scoring().is_err() {
        return None;
    }
    let pm = sc.price_model.as_ref()?;
    let digest = sc.price_model_digest.clone()?;
    let prices = arena_measure::cost::Prices::from_model(pm, chal.hardware_profile.vcpus);
    let runs = arena_measure::cost::class_runs_for(chal, &b.classes).ok()?;
    let point = arena_measure::cost::cost_score(
        &prices,
        &runs,
        b.prepare_ns,
        sc.cost_baseline_prepare_ns.unwrap_or(0),
    )
    .ok()?;
    let ci = b
        .cost
        .as_ref()
        .filter(|c| c.price_model_digest == digest)
        .and_then(|c| c.score_ci_milli);
    Some(arena_measure::cost::to_contract(pm, digest, &point, ci))
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
            verify_runs_ns: vec![],
            proof_bytes_runs: vec![],
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
            cost: None,
        }
    }
    #[test]
    fn baseline_equals_100() {
        assert_eq!(
            compute_score_milli(&br(vec![cm("a", 1_000_000, 50, 50)])),
            Some(100_000)
        );
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
    fn v1_6(cost: bool) -> ChallengeDefinition {
        let mut c: ChallengeDefinition = serde_json::from_str(include_str!(
            "../../../challenges/chl_7c0456cb2d1a36f8601863ac206cfcc9.json"
        ))
        .unwrap();
        if cost {
            let mut pm: arena_types::PriceModel = serde_json::from_str(include_str!(
                "../../../challenges/price-models/pm-near-mainnet-2026q4.draft.json"
            ))
            .unwrap();
            pm.status = "governed".into();
            c.scoring = Some(arena_types::ScoringSpec {
                kind: arena_types::ScoringKind::CostV1,
                price_model_digest: Some(pm.digest().unwrap()),
                price_model: Some(pm),
                cost_baseline: c
                    .workload_suite
                    .baseline_ns
                    .iter()
                    .map(|(id, ns)| arena_types::scoring::CostBaselineClass {
                        class_id: id.clone(),
                        prove_ns: *ns,
                        verify_ns: 40_000_000,
                        proof_bytes: 10_000,
                    })
                    .collect(),
                cost_baseline_prepare_ns: None,
            });
        }
        c
    }

    /// The reference candidate's own measurements, with a forged worker cost.
    fn reference_bench(c: &ChallengeDefinition) -> BenchmarkResult {
        let classes = c
            .workload_suite
            .baseline_ns
            .iter()
            .map(|(id, ns)| ClassMeasurement {
                class_id: id.clone(),
                weight_ppm: c
                    .workload_suite
                    .classes
                    .iter()
                    .find(|k| &k.id == id)
                    .unwrap()
                    .weight_ppm,
                runs_ns: vec![*ns; 3],
                median_ns: *ns,
                mad_ns: 0,
                cold_ns: None,
                baseline_ns: 0,
                verify_median_ns: 5_000_000,
                proof_bytes_max: 1_250,
                peak_rss_bytes: 1,
                verify_runs_ns: vec![40_000_000; 3],
                proof_bytes_runs: vec![10_000; 3],
            })
            .collect();
        let mut b = br(classes);
        b.suite_revision = c.workload_suite.revision.clone();
        b
    }

    #[test]
    fn server_recomputes_cost_and_keeps_kinds_apart() {
        let c = v1_6(true);
        let mut b = reference_bench(&c);
        let d = c
            .scoring
            .as_ref()
            .unwrap()
            .price_model_digest
            .clone()
            .unwrap();
        b.cost = Some(arena_types::CostResult {
            kind: arena_types::ScoringKind::CostV1,
            price_model_id: "forged".into(),
            price_model_digest: d,
            validators_per_chunk: 1,
            verifier_vcpus: 1,
            score_milli: Some(999_999_999),
            score_ci_milli: Some(7),
            classes: vec![],
        });
        let n = normalize_benchmark(&c, b.clone()).unwrap();
        let cost = n.cost.unwrap();
        assert_eq!(cost.score_milli, Some(100_000));
        assert_eq!(cost.score_ci_milli, Some(7));
        assert_eq!(cost.validators_per_chunk, 84);
        assert_eq!(cost.classes.len(), 3);
        assert_eq!(n.score_milli, Some(100_000));

        // Speed challenge: a worker-sent cost result is dropped.
        let s = v1_6(false);
        let n = normalize_benchmark(&s, b.clone()).unwrap();
        assert!(n.cost.is_none());

        // Old results without per-run verify/bytes: no cost score.
        let mut old = b;
        for k in &mut old.classes {
            k.verify_runs_ns.clear();
            k.proof_bytes_runs.clear();
        }
        assert!(normalize_benchmark(&c, old).unwrap().cost.is_none());
    }

    #[test]
    fn missing_baseline_no_score() {
        assert_eq!(
            compute_score_milli(&br(vec![cm("a", 1_000_000, 50, 0)])),
            None
        );
    }
}
