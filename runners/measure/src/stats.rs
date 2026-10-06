//! Portable integer statistics, the arena PRNG, seeds and run schedules
//! (docs/BENCHMARK_SPEC.md §5, §7, §8.3–8.4). Bit-exact with the reference
//! implementation `benchmarks/arena_bench`.

use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

/// SplitMix64 (Steele, Lea, Flood 2014). The only PRNG the arena uses.
#[derive(Clone, Debug)]
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        SplitMix64 { state: seed }
    }
    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// Index in `[0, n)`: `next_u64() % n` (modulo bias accepted, §8.3).
    pub fn below(&mut self, n: u64) -> u64 {
        assert!(n > 0, "n must be positive");
        self.next_u64() % n
    }
}

/// Integer median; even length: `lo + (hi - lo) / 2` (floor, no overflow).
/// `None` for an empty input.
pub fn median_u64(xs: &[u64]) -> Option<u64> {
    if xs.is_empty() {
        return None;
    }
    let mut s = xs.to_vec();
    s.sort_unstable();
    let n = s.len();
    Some(if n % 2 == 1 {
        s[n / 2]
    } else {
        let (lo, hi) = (s[n / 2 - 1], s[n / 2]);
        lo + (hi - lo) / 2
    })
}

/// Lower quartile as an order statistic: the element at index ⌊(n−1)/4⌋ of
/// the sorted input (no interpolation; n = 15 → 4th smallest, n = 25 → 7th).
/// `None` for an empty input. docs/BENCHMARK_SPEC.md §14.3.
pub fn lower_quartile_u64(xs: &[u64]) -> Option<u64> {
    if xs.is_empty() {
        return None;
    }
    let mut s = xs.to_vec();
    s.sort_unstable();
    Some(s[(s.len() - 1) / 4])
}

/// Verdict of the bench-spec-v1.6 calibration gate (§6.1) over the probes of
/// one session, in time order (pre, one per measured round, post).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProbeVerdict {
    pub n: u32,
    pub median_ns: u64,
    /// MAD / median, ppm, rounded up.
    pub noise_ppm: u64,
    /// Order statistic ⌊(m−1)·9/10⌋ of the m sorted consecutive drifts
    /// (`drift_ppm(q[i−1], q[i])`) of the rolling medians q of
    /// [`PROBE_SMOOTH`] consecutive probes (the raw probes when n < 3).
    pub step_p90_ppm: u64,
    /// `drift_ppm(p[0], p[n−1])`: informational (paired ratios cancel slow drift).
    pub session_drift_ppm: u64,
    pub reference_drift_ppm: Option<u64>,
    pub ok: bool,
    /// Any of `CALIBRATION_STEP`, `CALIBRATION_NOISY`, `REFERENCE_DRIFT`.
    pub reasons: Vec<String>,
}

/// Width of the rolling median the step gate is taken over: a single probe
/// carries ~2% of its own noise on the reference host (BENCHMARK_SPEC §6.1.1).
pub const PROBE_SMOOTH: usize = 3;

/// bench-spec-v1.6 calibration gate. A step gate (not a start-vs-end drift
/// gate): host changes slower than one round cancel out of the paired
/// reference ratio, so only a jump between consecutive probes, or a noisy
/// session as a whole, invalidates it. `Err` if fewer than 2 probes or a 0.
pub fn probe_verdict(
    probes: &[u64],
    max_step_ppm: u64,
    max_noise_ppm: u64,
    reference: Option<(u64, u64)>,
) -> Result<ProbeVerdict, String> {
    if probes.len() < 2 {
        return Err("calibration needs at least 2 probes".into());
    }
    if probes.contains(&0) {
        return Err("calibration probe of 0 ns".into());
    }
    let median = median_u64(probes).expect("non-empty");
    let mad = mad_u64(probes).expect("non-empty");
    let noise = drift_ppm(median, median + mad);
    let smooth: Vec<u64> = if probes.len() >= PROBE_SMOOTH {
        probes
            .windows(PROBE_SMOOTH)
            .map(|w| median_u64(w).expect("non-empty"))
            .collect()
    } else {
        probes.to_vec()
    };
    let mut steps: Vec<u64> = smooth.windows(2).map(|w| drift_ppm(w[0], w[1])).collect();
    if steps.is_empty() {
        steps.push(0);
    }
    steps.sort_unstable();
    let p90 = steps[(steps.len() - 1) * 9 / 10];
    let session = drift_ppm(probes[0], probes[probes.len() - 1]);
    let mut reasons = vec![];
    if p90 > max_step_ppm {
        reasons.push("CALIBRATION_STEP".to_string());
    }
    if noise > max_noise_ppm {
        reasons.push("CALIBRATION_NOISY".to_string());
    }
    let reference_drift = match reference {
        Some((ref_ns, max_ppm)) if ref_ns > 0 => {
            let d = drift_ppm(ref_ns, median);
            if d > max_ppm {
                reasons.push("REFERENCE_DRIFT".to_string());
            }
            Some(d)
        }
        _ => None,
    };
    Ok(ProbeVerdict {
        n: probes.len() as u32,
        median_ns: median,
        noise_ppm: noise,
        step_p90_ppm: p90,
        session_drift_ppm: session,
        reference_drift_ppm: reference_drift,
        ok: reasons.is_empty(),
        reasons,
    })
}

/// Unscaled median absolute deviation around [`median_u64`].
pub fn mad_u64(xs: &[u64]) -> Option<u64> {
    let m = median_u64(xs)?;
    let dev: Vec<u64> = xs.iter().map(|&x| x.abs_diff(m)).collect();
    median_u64(&dev)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OutlierReport {
    pub median_ns: u64,
    pub mad_ns: u64,
    pub k: u32,
    pub flagged_indices: Vec<usize>,
    /// Fraction of runs flagged, ppm (floor).
    pub flagged_ppm: u64,
    /// More than `max_flagged_ppm` flagged: re-measure the class (infra).
    pub excessive: bool,
    /// `MAD_ZERO` when MAD == 0 (reported, not special-cased).
    pub notes: Vec<String>,
}

pub const MAX_FLAGGED_PPM: u64 = 200_000;

/// Flag run `i` iff `|x_i - median| > k * MAD` (strict). Never drops runs.
pub fn flag_outliers(runs: &[u64], k: u32) -> Option<OutlierReport> {
    let med = median_u64(runs)?;
    let mad = mad_u64(runs)?;
    let thr = (k as u128) * (mad as u128);
    let flagged: Vec<usize> = runs
        .iter()
        .enumerate()
        .filter(|(_, &x)| (x.abs_diff(med) as u128) > thr)
        .map(|(i, _)| i)
        .collect();
    let ppm = flagged.len() as u64 * 1_000_000 / runs.len() as u64;
    Some(OutlierReport {
        median_ns: med,
        mad_ns: mad,
        k,
        flagged_ppm: ppm,
        excessive: ppm > MAX_FLAGGED_PPM,
        notes: if mad == 0 {
            vec!["MAD_ZERO".into()]
        } else {
            vec![]
        },
        flagged_indices: flagged,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TripwireResult {
    pub suspected: bool,
    pub measured_median_ns: u64,
    pub fresh_median_ns: u64,
    pub slowdown_ppm: u64,
}

pub const TRIPWIRE_MIN_SLOWDOWN_PPM: u64 = 50_000;

/// Fresh-input caching tripwire (§7.4): suspected iff the fresh median is
/// slower than the steady-state median by more than both `k * MAD` and
/// 50 000 ppm.
pub fn caching_tripwire(measured: &[u64], fresh: &[u64], k: u32) -> Option<TripwireResult> {
    let med = median_u64(measured)?;
    let mad = mad_u64(measured)?;
    let fr = median_u64(fresh)?;
    let delta = fr as i128 - med as i128;
    let slowdown_ppm = if med == 0 {
        0
    } else {
        (delta.max(0) as u128 * 1_000_000 / med as u128) as u64
    };
    let suspected = delta > (k as i128) * (mad as i128) && slowdown_ppm > TRIPWIRE_MIN_SLOWDOWN_PPM;
    Some(TripwireResult {
        suspected,
        measured_median_ns: med,
        fresh_median_ns: fr,
        slowdown_ppm,
    })
}

/// `|b - a| / a` in ppm, integer, rounded up. `a` must be > 0.
pub fn drift_ppm(a: u64, b: u64) -> u64 {
    assert!(a > 0);
    let num = b.abs_diff(a) as u128 * 1_000_000;
    num.div_ceil(a as u128) as u64
}

fn seed_part_ok(p: &str) -> bool {
    p.bytes().all(|b| (0x21..=0x7e).contains(&b) && b != b'|')
}

/// Public seed: first 8 bytes (big-endian) of
/// `sha256("near-arena-seed-v1|<purpose>|<part1>|...")`.
pub fn derive_seed(purpose: &str, parts: &[&str]) -> Result<u64, String> {
    let mut msg = String::from("near-arena-seed-v1|");
    if !seed_part_ok(purpose) {
        return Err(format!("bad seed purpose {purpose:?}"));
    }
    msg.push_str(purpose);
    for p in parts {
        if !seed_part_ok(p) {
            return Err(format!("bad seed part {p:?}"));
        }
        msg.push('|');
        msg.push_str(p);
    }
    let h = Sha256::digest(msg.as_bytes());
    Ok(u64::from_be_bytes(h[..8].try_into().unwrap()))
}

/// Fisher-Yates: `for i in n-1 down to 1: j = below(i+1); swap(i, j)`.
pub fn shuffle<T>(items: &mut [T], rng: &mut SplitMix64) {
    for i in (1..items.len()).rev() {
        let j = rng.below(i as u64 + 1) as usize;
        items.swap(i, j);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Phase {
    CalibrationPre,
    Cold,
    Warmup,
    Measured,
    FreshConfirm,
    CalibrationPost,
}

impl Phase {
    pub fn as_str(self) -> &'static str {
        match self {
            Phase::CalibrationPre => "calibration_pre",
            Phase::Cold => "cold",
            Phase::Warmup => "warmup",
            Phase::Measured => "measured",
            Phase::FreshConfirm => "fresh_confirm",
            Phase::CalibrationPost => "calibration_post",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScheduledRun {
    pub seq: usize,
    pub phase: Phase,
    /// Empty for calibration entries.
    pub class_id: String,
    pub round: u32,
}

#[derive(Clone, Copy, Debug)]
pub struct ScheduleShape {
    pub cold_runs: u32,
    pub warmup_runs: u32,
    pub measured_runs: u32,
    pub fresh_confirm_runs: u32,
    pub calibration_runs: u32,
}

/// Session layout (§5): every round of a non-calibration phase is an
/// independent permutation of the class ids (sorted by UTF-8 bytes first),
/// drawn from one SplitMix64(seed) stream in schedule order.
pub fn build_schedule(
    class_ids: &[String],
    seed: u64,
    shape: ScheduleShape,
) -> Result<Vec<ScheduledRun>, String> {
    let mut base: Vec<String> = class_ids.to_vec();
    base.sort();
    let n = base.len();
    base.dedup();
    if base.is_empty() || base.len() != n {
        return Err("class ids must be non-empty and unique".into());
    }
    let mut rng = SplitMix64::new(seed);
    let mut out = Vec::new();
    let emit = |out: &mut Vec<ScheduledRun>, phase, class_id: String, round| {
        let seq = out.len();
        out.push(ScheduledRun {
            seq,
            phase,
            class_id,
            round,
        });
    };
    for r in 0..shape.calibration_runs {
        emit(&mut out, Phase::CalibrationPre, String::new(), r);
    }
    for (phase, rounds) in [
        (Phase::Cold, shape.cold_runs),
        (Phase::Warmup, shape.warmup_runs),
        (Phase::Measured, shape.measured_runs),
        (Phase::FreshConfirm, shape.fresh_confirm_runs),
    ] {
        for r in 0..rounds {
            let mut perm = base.clone();
            shuffle(&mut perm, &mut rng);
            for c in perm {
                emit(&mut out, phase, c, r);
            }
        }
    }
    for r in 0..shape.calibration_runs {
        emit(&mut out, Phase::CalibrationPost, String::new(), r);
    }
    Ok(out)
}
