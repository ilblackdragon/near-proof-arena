//! Cost-normalized score (`cost_v1`) — docs/BENCHMARK_SPEC.md §14. Pure
//! integer cost arithmetic plus the §8 score formula applied to per-class
//! costs; bit-exact with `benchmarks/arena_bench/cost.py` on every integer
//! output (vectors: `benchmarks/testvectors/cost.json`).
//!
//! ```text
//! per class j, component medians over measured runs (one run = one batch):
//!   P = median(prove_runs_ns)   V = median(verify_runs_ns)   S = median(proof_bytes_runs)
//! prove_fusd     = ceil(P · vcpus_p · c_cpu / 1e9)
//! prepare_fusd   = A == 0 ? 0 : ceil(prepare_ns · vcpus_p · c_cpu · batch_size / (1e9 · A))
//! verify_fusd    = N_v · ceil(V · vcpus_v · c_cpu / 1e9)
//! bandwidth_fusd = N_v · S · c_bw
//! storage_fusd   = N_v · S · c_store
//! total          = Σ of the five (u64, COST_OVERFLOW otherwise; > 0)
//! score          = §8 score with baseline_ns := baseline total, median_ns := candidate total
//! ```
//! Bootstrap: like §8.3, but one index draw per element resamples the run
//! *triple* (P, V, S) jointly, and the three medians are taken over it.

use crate::score::{self, ClassInput, ScoreError};
use crate::stats::{median_u64, SplitMix64};
use serde::{Deserialize, Serialize};

const NS_PER_S: u128 = 1_000_000_000;

/// The price-model numbers the formula needs (`arena_types::PriceModel`
/// minus labels), plus the prover's vCPU count from the hardware profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Prices {
    pub validators_per_chunk: u32,
    pub prover_vcpus: u32,
    pub verifier_vcpus: u32,
    pub cpu_fusd_per_vcpu_second: u64,
    pub bandwidth_fusd_per_byte: u64,
    pub storage_fusd_per_byte: u64,
    pub prepare_amortization_requests: u64,
}

impl Prices {
    pub fn from_model(pm: &arena_types::PriceModel, prover_vcpus: u32) -> Self {
        Prices {
            validators_per_chunk: pm.validators_per_chunk,
            prover_vcpus,
            verifier_vcpus: pm.verifier_vcpus,
            cpu_fusd_per_vcpu_second: pm.cpu_fusd_per_vcpu_second,
            bandwidth_fusd_per_byte: pm.bandwidth_fusd_per_byte,
            storage_fusd_per_byte: pm.storage_fusd_per_byte,
            prepare_amortization_requests: pm.prepare_amortization_requests,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, thiserror::Error)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum CostError {
    #[error("BAD_PRICES")]
    BadPrices,
    #[error("ZERO_OR_BAD_TIME")]
    ZeroOrBadTime,
    #[error("ZERO_COST")]
    ZeroCost,
    #[error("COST_OVERFLOW")]
    CostOverflow,
    #[error("RUN_LENGTH_MISMATCH")]
    RunLengthMismatch,
    #[error("MISSING_BASELINE")]
    MissingBaseline,
    #[error("{0}")]
    Score(ScoreError),
}

impl CostError {
    pub fn code(self) -> &'static str {
        match self {
            CostError::BadPrices => "BAD_PRICES",
            CostError::ZeroOrBadTime => "ZERO_OR_BAD_TIME",
            CostError::ZeroCost => "ZERO_COST",
            CostError::CostOverflow => "COST_OVERFLOW",
            CostError::RunLengthMismatch => "RUN_LENGTH_MISMATCH",
            CostError::MissingBaseline => "MISSING_BASELINE",
            CostError::Score(e) => e.code(),
        }
    }
}

impl From<ScoreError> for CostError {
    fn from(e: ScoreError) -> Self {
        CostError::Score(e)
    }
}

/// Measured cost components of one batch run (or their medians).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Components {
    pub prove_ns: u64,
    pub verify_ns: u64,
    pub proof_bytes: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Breakdown {
    pub prove_fusd: u64,
    pub prepare_fusd: u64,
    pub verify_fusd: u64,
    pub bandwidth_fusd: u64,
    pub storage_fusd: u64,
    pub total_fusd: u64,
}

fn ceil_div(a: u128, b: u128) -> u128 {
    a.div_ceil(b)
}

fn to_u64(x: u128) -> Result<u64, CostError> {
    u64::try_from(x).map_err(|_| CostError::CostOverflow)
}

/// Cost of one batch run of `batch_size` requests (normative integer formula).
pub fn batch_cost(
    p: &Prices,
    c: Components,
    prepare_ns: u64,
    batch_size: u32,
) -> Result<Breakdown, CostError> {
    if p.validators_per_chunk == 0
        || p.prover_vcpus == 0
        || p.verifier_vcpus == 0
        || p.cpu_fusd_per_vcpu_second == 0
    {
        return Err(CostError::BadPrices);
    }
    if c.prove_ns == 0 || c.verify_ns == 0 {
        return Err(CostError::ZeroOrBadTime);
    }
    let cpu = p.cpu_fusd_per_vcpu_second as u128;
    let nv = p.validators_per_chunk as u128;
    // u64·u32·u64 can exceed u128: every product is checked.
    let mul = |a: u128, b: u128| a.checked_mul(b).ok_or(CostError::CostOverflow);
    let prove = ceil_div(
        mul(mul(c.prove_ns as u128, p.prover_vcpus as u128)?, cpu)?,
        NS_PER_S,
    );
    let prepare = if p.prepare_amortization_requests == 0 {
        0
    } else {
        ceil_div(
            mul(
                mul(mul(prepare_ns as u128, p.prover_vcpus as u128)?, cpu)?,
                batch_size as u128,
            )?,
            mul(NS_PER_S, p.prepare_amortization_requests as u128)?,
        )
    };
    let verify_one = ceil_div(
        mul(mul(c.verify_ns as u128, p.verifier_vcpus as u128)?, cpu)?,
        NS_PER_S,
    );
    let verify = mul(nv, verify_one)?;
    let bandwidth = mul(
        nv,
        mul(c.proof_bytes as u128, p.bandwidth_fusd_per_byte as u128)?,
    )?;
    let storage = mul(
        nv,
        mul(c.proof_bytes as u128, p.storage_fusd_per_byte as u128)?,
    )?;
    let parts = [
        to_u64(prove)?,
        to_u64(prepare)?,
        to_u64(verify)?,
        to_u64(bandwidth)?,
        to_u64(storage)?,
    ];
    let total = parts
        .iter()
        .try_fold(0u64, |a, &x| a.checked_add(x))
        .ok_or(CostError::CostOverflow)?;
    let b = Breakdown {
        prove_fusd: parts[0],
        prepare_fusd: parts[1],
        verify_fusd: parts[2],
        bandwidth_fusd: parts[3],
        storage_fusd: parts[4],
        total_fusd: total,
    };
    if b.total_fusd == 0 {
        return Err(CostError::ZeroCost);
    }
    Ok(b)
}

/// Measured runs of one class for the cost score.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CostClassRuns {
    pub class_id: String,
    pub weight_ppm: u32,
    pub batch_size: u32,
    /// Reference candidate's component medians (`scoring.cost_baseline`).
    pub baseline: Components,
    pub prove_runs_ns: Vec<u64>,
    pub verify_runs_ns: Vec<u64>,
    pub proof_bytes_runs: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CostClassResult {
    pub class_id: String,
    pub weight_ppm: u32,
    pub medians: Components,
    pub cost: Breakdown,
    pub baseline_total_fusd: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CostScore {
    pub score_milli: u64,
    pub classes: Vec<CostClassResult>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CostBootstrap {
    pub score_milli: u64,
    pub lo_milli: u64,
    pub hi_milli: u64,
    pub half_width_milli: u64,
    pub iterations: u32,
    pub seed: u64,
}

fn check_runs(c: &CostClassRuns) -> Result<usize, CostError> {
    let n = c.prove_runs_ns.len();
    if n == 0 {
        return Err(ScoreError::NoRuns.into());
    }
    if c.verify_runs_ns.len() != n || c.proof_bytes_runs.len() != n {
        return Err(CostError::RunLengthMismatch);
    }
    Ok(n)
}

fn medians(c: &CostClassRuns) -> Components {
    Components {
        prove_ns: median_u64(&c.prove_runs_ns).expect("checked"),
        verify_ns: median_u64(&c.verify_runs_ns).expect("checked"),
        proof_bytes: median_u64(&c.proof_bytes_runs).expect("checked"),
    }
}

fn baseline_total(
    p: &Prices,
    c: &CostClassRuns,
    baseline_prepare_ns: u64,
) -> Result<u64, CostError> {
    Ok(batch_cost(p, c.baseline, baseline_prepare_ns, c.batch_size)?.total_fusd)
}

/// Cost score of the component medians (point estimate). Class validation
/// (ids, duplicates, weight sum) is the §8 score's.
pub fn cost_score(
    p: &Prices,
    classes: &[CostClassRuns],
    prepare_ns: u64,
    baseline_prepare_ns: u64,
) -> Result<CostScore, CostError> {
    let mut out = Vec::with_capacity(classes.len());
    let mut inputs = Vec::with_capacity(classes.len());
    for c in classes {
        check_runs(c)?;
        let m = medians(c);
        let cost = batch_cost(p, m, prepare_ns, c.batch_size)?;
        let base = baseline_total(p, c, baseline_prepare_ns)?;
        inputs.push(ClassInput {
            class_id: c.class_id.clone(),
            weight_ppm: c.weight_ppm,
            baseline_ns: base,
            median_ns: cost.total_fusd,
        });
        out.push(CostClassResult {
            class_id: c.class_id.clone(),
            weight_ppm: c.weight_ppm,
            medians: m,
            cost,
            baseline_total_fusd: base,
        });
    }
    let s = score::score(&inputs)?;
    Ok(CostScore {
        score_milli: s.score_milli,
        classes: out,
    })
}

/// Seeded percentile bootstrap of the cost score (§14.3).
pub fn cost_bootstrap(
    p: &Prices,
    classes: &[CostClassRuns],
    prepare_ns: u64,
    baseline_prepare_ns: u64,
    seed: u64,
    iterations: u32,
) -> Result<CostBootstrap, CostError> {
    assert!(iterations >= 1, "iterations must be >= 1");
    let point = cost_score(p, classes, prepare_ns, baseline_prepare_ns)?;
    let mut ordered: Vec<&CostClassRuns> = classes.iter().collect();
    ordered.sort_by(|a, b| a.class_id.as_bytes().cmp(b.class_id.as_bytes()));
    let bases: Vec<u64> = ordered
        .iter()
        .map(|c| baseline_total(p, c, baseline_prepare_ns))
        .collect::<Result<_, _>>()?;
    let mut rng = SplitMix64::new(seed);
    let mut xs = Vec::with_capacity(iterations as usize);
    let (mut bp, mut bv, mut bs) = (Vec::new(), Vec::new(), Vec::new());
    for _ in 0..iterations {
        let mut inputs = Vec::with_capacity(ordered.len());
        for (c, base) in ordered.iter().zip(&bases) {
            let n = c.prove_runs_ns.len() as u64;
            bp.clear();
            bv.clear();
            bs.clear();
            for _ in 0..n {
                let i = rng.below(n) as usize;
                bp.push(c.prove_runs_ns[i]);
                bv.push(c.verify_runs_ns[i]);
                bs.push(c.proof_bytes_runs[i]);
            }
            let m = Components {
                prove_ns: median_u64(&bp).expect("non-empty"),
                verify_ns: median_u64(&bv).expect("non-empty"),
                proof_bytes: median_u64(&bs).expect("non-empty"),
            };
            inputs.push(ClassInput {
                class_id: c.class_id.clone(),
                weight_ppm: c.weight_ppm,
                baseline_ns: *base,
                median_ns: batch_cost(p, m, prepare_ns, c.batch_size)?.total_fusd,
            });
        }
        xs.push(score::score(&inputs)?.score_milli);
    }
    xs.sort_unstable();
    let b = iterations as usize;
    let lo = xs[((b - 1) * 25) / 1000];
    let hi = xs[((b - 1) * 975).div_ceil(1000)];
    Ok(CostBootstrap {
        score_milli: point.score_milli,
        lo_milli: lo,
        hi_milli: hi,
        half_width_milli: (hi - lo).div_ceil(2),
        iterations,
        seed,
    })
}

/// Verify drift control tolerance (docs/BENCHMARK_SPEC.md §14.4): the
/// §6.2 paired-control tolerance, applied to verify medians.
pub const VERIFY_CONTROL_TOLERANCE_PPM: u64 = 30_000;

/// One class of a [`VerifyControl`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifyControlClass {
    pub class_id: String,
    /// The pinned reference verify median per batch (`cost_baseline.verify_ns`).
    pub pinned_verify_ns: u64,
    /// Median of the control session's per-run verify totals.
    pub control_verify_ns: u64,
    /// `|control - pinned| / pinned` in ppm, rounded up.
    pub drift_ppm: u64,
    pub ok: bool,
}

/// Verdict of the verify drift control (§14.4): a control session of the
/// reference candidate on the same CPUs must reproduce every class's pinned
/// verify median within `tolerance_ppm`. A failure (`VERIFY_DRIFT`) makes
/// the session infra-invalid; it is never charged to a candidate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifyControl {
    pub tolerance_ppm: u64,
    /// Sorted by class id (bytes).
    pub classes: Vec<VerifyControlClass>,
    pub ok: bool,
    /// Empty, or `["VERIFY_DRIFT"]`.
    pub reasons: Vec<String>,
}

/// Normative verify drift control. `pinned` and `control_runs` must name the
/// same classes (`MISSING_BASELINE` otherwise); every control class needs at
/// least one run (`NO_RUNS`) and every pinned median must be > 0
/// (`ZERO_OR_BAD_TIME`).
pub fn verify_control(
    pinned: &[(String, u64)],
    control_runs: &[(String, Vec<u64>)],
    tolerance_ppm: u64,
) -> Result<VerifyControl, CostError> {
    let mut ids: Vec<&str> = pinned.iter().map(|(c, _)| c.as_str()).collect();
    ids.sort_unstable_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    let mut ctl: Vec<&str> = control_runs.iter().map(|(c, _)| c.as_str()).collect();
    ctl.sort_unstable_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    if ids != ctl || ids.windows(2).any(|w| w[0] == w[1]) {
        return Err(CostError::MissingBaseline);
    }
    let mut classes = Vec::with_capacity(ids.len());
    for id in ids {
        let pin = pinned.iter().find(|(c, _)| c == id).expect("same ids").1;
        let runs = &control_runs
            .iter()
            .find(|(c, _)| c == id)
            .expect("same ids")
            .1;
        if pin == 0 {
            return Err(CostError::ZeroOrBadTime);
        }
        let med = median_u64(runs).ok_or(CostError::Score(ScoreError::NoRuns))?;
        let drift = crate::stats::drift_ppm(pin, med);
        classes.push(VerifyControlClass {
            class_id: id.to_string(),
            pinned_verify_ns: pin,
            control_verify_ns: med,
            drift_ppm: drift,
            ok: drift <= tolerance_ppm,
        });
    }
    let ok = classes.iter().all(|c| c.ok);
    Ok(VerifyControl {
        tolerance_ppm,
        classes,
        ok,
        reasons: if ok {
            vec![]
        } else {
            vec!["VERIFY_DRIFT".into()]
        },
    })
}

/// Build the contract-level [`arena_types::CostResult`] from a point score
/// (and an optional CI half-width).
pub fn to_contract(
    pm: &arena_types::PriceModel,
    digest: arena_types::Digest,
    s: &CostScore,
    ci_milli: Option<u64>,
) -> arena_types::CostResult {
    arena_types::CostResult {
        kind: arena_types::ScoringKind::CostV1,
        price_model_id: format!("{}@v{}", pm.id, pm.version),
        price_model_digest: digest,
        validators_per_chunk: pm.validators_per_chunk,
        verifier_vcpus: pm.verifier_vcpus,
        score_milli: Some(s.score_milli),
        score_ci_milli: ci_milli,
        classes: s
            .classes
            .iter()
            .map(|c| arena_types::CostClass {
                class_id: c.class_id.clone(),
                weight_ppm: c.weight_ppm,
                prove_ns: c.medians.prove_ns,
                verify_ns: c.medians.verify_ns,
                proof_bytes: c.medians.proof_bytes,
                prove_fusd: c.cost.prove_fusd,
                prepare_fusd: c.cost.prepare_fusd,
                verify_fusd: c.cost.verify_fusd,
                bandwidth_fusd: c.cost.bandwidth_fusd,
                storage_fusd: c.cost.storage_fusd,
                total_fusd: c.cost.total_fusd,
                baseline_total_fusd: c.baseline_total_fusd,
            })
            .collect(),
    }
}

/// Assemble [`CostClassRuns`] from a challenge with `scoring.kind = cost_v1`
/// and per-class measurements. Errors name the missing piece.
pub fn class_runs_for(
    chal: &arena_types::ChallengeDefinition,
    classes: &[arena_types::ClassMeasurement],
) -> Result<Vec<CostClassRuns>, CostError> {
    let sc = chal.scoring.as_ref().ok_or(CostError::MissingBaseline)?;
    classes
        .iter()
        .map(|m| {
            let wc = chal
                .workload_suite
                .classes
                .iter()
                .find(|c| c.id == m.class_id)
                .ok_or(CostError::MissingBaseline)?;
            let b = sc
                .cost_baseline
                .iter()
                .find(|b| b.class_id == m.class_id)
                .ok_or(CostError::MissingBaseline)?;
            Ok(CostClassRuns {
                class_id: m.class_id.clone(),
                weight_ppm: m.weight_ppm,
                batch_size: wc.batch_size,
                baseline: Components {
                    prove_ns: b.prove_ns,
                    verify_ns: b.verify_ns,
                    proof_bytes: b.proof_bytes,
                },
                prove_runs_ns: m.runs_ns.clone(),
                verify_runs_ns: m.verify_runs_ns.clone(),
                proof_bytes_runs: m.proof_bytes_runs.clone(),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prices() -> Prices {
        Prices {
            validators_per_chunk: 100,
            prover_vcpus: 8,
            verifier_vcpus: 8,
            cpu_fusd_per_vcpu_second: 7_610_000_000,
            bandwidth_fusd_per_byte: 83_500,
            storage_fusd_per_byte: 0,
            prepare_amortization_requests: 0,
        }
    }
    fn runs(
        id: &str,
        w: u32,
        base: (u64, u64, u64),
        p: &[u64],
        v: &[u64],
        s: &[u64],
    ) -> CostClassRuns {
        CostClassRuns {
            class_id: id.into(),
            weight_ppm: w,
            batch_size: 8,
            baseline: Components {
                prove_ns: base.0,
                verify_ns: base.1,
                proof_bytes: base.2,
            },
            prove_runs_ns: p.to_vec(),
            verify_runs_ns: v.to_vec(),
            proof_bytes_runs: s.to_vec(),
        }
    }

    #[test]
    fn baseline_against_itself_is_100() {
        let c = runs(
            "a",
            1_000_000,
            (10, 20, 30),
            &[10, 9, 11],
            &[20, 21, 19],
            &[30, 30, 30],
        );
        assert_eq!(
            cost_score(&prices(), &[c], 0, 0).unwrap().score_milli,
            100_000
        );
    }

    #[test]
    fn halving_every_component_doubles_the_score() {
        let p = Prices {
            bandwidth_fusd_per_byte: 1_000,
            ..prices()
        };
        // Choose values for which ceil() is exact so halving is exact.
        let c = runs(
            "a",
            1_000_000,
            (2_000_000_000, 4_000_000_000, 2_000),
            &[1_000_000_000],
            &[2_000_000_000],
            &[1_000],
        );
        assert_eq!(cost_score(&p, &[c], 0, 0).unwrap().score_milli, 200_000);
    }

    #[test]
    fn components_sum_and_nv_factor() {
        let b = batch_cost(
            &prices(),
            Components {
                prove_ns: 1_000_000_000,
                verify_ns: 1,
                proof_bytes: 10,
            },
            0,
            8,
        )
        .unwrap();
        assert_eq!(b.prove_fusd, 8 * 7_610_000_000);
        // ceil(1 ns · 8 · 7.61e9 / 1e9) = 61 per validator
        assert_eq!(b.verify_fusd, 100 * 61);
        assert_eq!(b.bandwidth_fusd, 100 * 10 * 83_500);
        assert_eq!(
            b.total_fusd,
            b.prove_fusd + b.prepare_fusd + b.verify_fusd + b.bandwidth_fusd + b.storage_fusd
        );
    }

    #[test]
    fn errors() {
        let p = prices();
        let z = Components {
            prove_ns: 1,
            verify_ns: 0,
            proof_bytes: 0,
        };
        assert_eq!(
            batch_cost(&p, z, 0, 1).unwrap_err(),
            CostError::ZeroOrBadTime
        );
        let big = Components {
            prove_ns: u64::MAX,
            verify_ns: u64::MAX,
            proof_bytes: u64::MAX,
        };
        assert_eq!(
            batch_cost(&p, big, 0, 1).unwrap_err(),
            CostError::CostOverflow
        );
        let mut c = runs("a", 1_000_000, (1, 1, 1), &[1, 2], &[1], &[1, 1]);
        assert_eq!(
            cost_score(&p, &[c.clone()], 0, 0).unwrap_err(),
            CostError::RunLengthMismatch
        );
        c.prove_runs_ns.clear();
        c.verify_runs_ns.clear();
        c.proof_bytes_runs.clear();
        assert_eq!(cost_score(&p, &[c], 0, 0).unwrap_err().code(), "NO_RUNS");
    }

    #[test]
    fn verify_control_tolerance() {
        let pin = vec![("a".to_string(), 1_000_000), ("b".to_string(), 2_000_000)];
        let ok = verify_control(
            &pin,
            &[
                ("b".into(), vec![2_050_000, 2_060_000, 1_990_000]),
                ("a".into(), vec![1_030_000, 990_000, 1_000_000]),
            ],
            VERIFY_CONTROL_TOLERANCE_PPM,
        )
        .unwrap();
        assert!(ok.ok && ok.reasons.is_empty());
        assert_eq!(ok.classes[0].class_id, "a");
        assert_eq!(ok.classes[1].drift_ppm, 25_000);
        // exactly at the tolerance passes; one ns above fails
        let edge = |v: u64| {
            verify_control(&pin[..1], &[("a".into(), vec![v])], 30_000)
                .unwrap()
                .ok
        };
        assert!(edge(1_030_000) && edge(970_000));
        assert!(!edge(1_030_001) && !edge(969_999));
        let bad = verify_control(&pin[..1], &[("a".into(), vec![1_031_000])], 30_000).unwrap();
        assert_eq!(bad.reasons, ["VERIFY_DRIFT"]);
        assert_eq!(
            verify_control(&pin, &[("a".into(), vec![1])], 30_000).unwrap_err(),
            CostError::MissingBaseline
        );
        assert_eq!(
            verify_control(&pin[..1], &[("a".into(), vec![])], 30_000)
                .unwrap_err()
                .code(),
            "NO_RUNS"
        );
    }

    #[test]
    fn bootstrap_is_order_independent() {
        let a = runs(
            "a",
            400_000,
            (100, 1000, 50),
            &[90, 95, 120, 100],
            &[900, 1100, 950, 1000],
            &[50, 50, 50, 50],
        );
        let b = runs(
            "b",
            600_000,
            (200, 5000, 900),
            &[210, 190, 205, 220],
            &[4000, 6000, 4500, 5100],
            &[800, 800, 800, 800],
        );
        let x = cost_bootstrap(&prices(), &[a.clone(), b.clone()], 0, 0, 7, 200).unwrap();
        let y = cost_bootstrap(&prices(), &[b, a], 0, 0, 7, 200).unwrap();
        assert_eq!(x, y);
        assert!(x.lo_milli <= x.score_milli && x.score_milli <= x.hi_milli);
    }
}
