//! Concrete soundness estimate for the configured proof system.
//!
//! This is *not* a certified bound: it evaluates Plonky3's own (unverified,
//! f64) security calculator (`p3-security` / `p3_uni_stark::{ProvenSecurity,
//! ConjecturedSecurity}`, rev 3acc8b70) on the exact shape of every table of
//! this AIR, adds the LogUp fingerprint term (`p3_security::logup`), and
//! composes them by a union bound. Formula per table `i` (bits = -log2 ε):
//!
//! * `proven_udr_i`, `proven_ldr_i`: ePrint 2024/1553 Thms 2/3 (round-by-round
//!   soundness of the DEEP-ALI + FRI STARK), unique-decoding resp. Johnson
//!   (list-decoding) regime, the latter using the DKT26 line-MCA bound
//!   (ePrint 2026/2056 Thm 5.12); composed of the ALI term, the DEEP term,
//!   the FRI commit/query terms, and the opening-batching term over the whole
//!   batch's `num_batched_functions`;
//! * `conj_i`: the ethSTARK-style "random words" conjecture (2025/2010 §1.5);
//! * all three are capped at the commitment hash's collision resistance
//!   (`CR` = 128 bits for SHA-256; we also report them with the cap lifted).
//!
//! Batch composition: ε_rbr = Σ_i ε_i + ε_logup with each table's ε_i computed
//! with the collision cap lifted (conservative: the shared FRI term is counted
//! once per table); the reported total is min(128, -log2 ε_rbr), where
//! ε_logup = N (W + 2) / |EF| with N = Σ_i interactions_i · height_i and W the
//! widest bus message (p3_security::logup).
//!
//! Fiat–Shamir with a hash-query budget q_H (the arena profile's accounting,
//! `security/README.md`): Adv ≤ (q_H + 1)·ε_rbr + q_H² / 2^256 (Merkle /
//! transcript collisions). With q_H = 2^64 this is at best ≈ 2^-128 from the
//! collision term alone and needs ε_rbr ≤ 2^-192.

use crate::air::{NpAir, all_airs};
use crate::config::*;
use p3_air::{AirLayout, BaseAir};
use p3_batch_stark::ProverData;
use p3_lookup::InteractionSymbolicBuilder;
use p3_security::GrindingSites;
use p3_security::fri::FriRegime;
use p3_security::logup::{LogUpAir, fingerprint_error};
use p3_security::shape::InstanceShape;
use p3_uni_stark::{ConjecturedSecurity, OpeningShape, ProvenSecurity, StarkSecurityParams};

pub const EXT_BITS: usize = 31 * EXT_DEGREE - 1; // log2|EF| lower bound (248 bits field, 247.x)

#[derive(Clone, Debug)]
pub struct TableShape {
    pub name: &'static str,
    pub log_n: usize,
    pub num_constraints: usize,
    pub max_degree: usize,
    pub num_quotient_chunks: usize,
    pub main_width: usize,
    pub main_next: bool,
    pub pre_width: usize,
    pub aux_cols: usize,
    pub interactions: usize,
    pub max_msg_width: usize,
}

pub fn table_shapes(degree_bits: &[usize]) -> Vec<TableShape> {
    let airs = all_airs();
    let config = make_config();
    let budgets: Vec<usize> = airs.iter().map(|a| a.lookup_budget()).collect();
    let pd = ProverData::from_airs_and_degrees_with_lookup_budgets(
        &config,
        &airs,
        degree_bits,
        &budgets,
        LOG_BLOWUP,
    )
    .expect("prover data");
    airs.iter()
        .enumerate()
        .map(|(i, a)| {
            let layout = AirLayout {
                preprocessed_width: BaseAir::<Val>::preprocessed_width(a),
                main_width: BaseAir::<Val>::width(a),
                num_public_values: a.num_pv(),
                ..Default::default()
            };
            let sb = InteractionSymbolicBuilder::<Val, Challenge>::from_air(a, layout);
            let inter = sb.global_interactions();
            let max_w = inter.iter().map(|x| x.fields.len()).max().unwrap_or(0);
            let lq = p3_batch_stark::symbolic::get_log_num_quotient_chunks::<Val, Challenge, _, _>(
                a,
                layout,
                1usize << degree_bits[i],
                &pd.common.lookups[i],
                0,
                &p3_lookup::LogUpGadget::new(),
            );
            let nl = pd.common.lookups[i].len();
            TableShape {
                name: a.name(),
                log_n: degree_bits[i],
                num_constraints: sb.base_constraints().len() + nl + 2,
                max_degree: (1usize << lq) + 1,
                num_quotient_chunks: 1usize << lq,
                main_width: layout.main_width,
                main_next: a.uses_next(),
                pre_width: layout.preprocessed_width,
                aux_cols: if nl == 0 { 0 } else { nl + 1 },
                interactions: inter.len(),
                max_msg_width: max_w,
            }
        })
        .collect()
}

#[derive(Clone, Debug)]
pub struct Bits {
    pub proven_udr: f64,
    pub proven_ldr: f64,
    pub conjectured: f64,
}

#[derive(Clone, Debug)]
pub struct Report {
    pub num_queries: usize,
    pub query_pow: usize,
    pub per_table: Vec<(&'static str, Bits)>,
    pub logup_bits: f64,
    /// Union-bound composites, CR-capped at 128 bits.
    pub total: Bits,
    /// Same with the SHA-256 collision cap lifted (round-by-round error only).
    pub total_rbr: Bits,
}

fn combine(bits: &[f64]) -> f64 {
    let s: f64 = bits.iter().map(|b| (2f64).powf(-b)).sum();
    -s.log2()
}

pub fn report(shapes: &[TableShape], num_queries: usize, query_pow: usize) -> Report {
    let total_batched: usize = shapes
        .iter()
        .map(|s| {
            p3_batch_stark::security::num_batched_openings(
                s.main_width,
                s.main_next,
                s.pre_width,
                false,
                s.num_quotient_chunks,
                if s.aux_cols > 0 { s.aux_cols - 1 } else { 0 },
                EXT_DEGREE,
                OpeningShape::new(),
            )
        })
        .sum();
    let fri = FriRegime {
        log_blowup: LOG_BLOWUP,
        num_queries,
        log_final_poly_len: LOG_FINAL_POLY_LEN,
        max_log_arity: MAX_LOG_ARITY,
        commit_pow_bits: COMMIT_POW_BITS,
        query_pow_bits: query_pow,
    };
    let mut per_table = vec![];
    let mut caps: [Vec<f64>; 3] = [vec![], vec![], vec![]];
    let mut rbrs: [Vec<f64>; 3] = [vec![], vec![], vec![]];
    for s in shapes {
        let mut out = [0f64; 6];
        for (ci, cr) in [128usize, 512].iter().enumerate() {
            let p = StarkSecurityParams::new(
                fri,
                EXT_BITS,
                *cr,
                s.num_constraints,
                s.max_degree.min((1 << LOG_BLOWUP) + 1),
                if s.main_next { 2 } else { 1 },
                total_batched,
                s.num_quotient_chunks,
            )
            .with_grinding(GrindingSites {
                batch_combination: BATCH_POW_BITS,
                ..GrindingSites::NONE
            });
            let pr = ProvenSecurity::compute_from_proof(s.log_n, &p);
            let cj = ConjecturedSecurity::compute_from_params(&p, s.log_n);
            out[3 * ci] = pr.unique_decoding_bits as f64;
            out[3 * ci + 1] = pr.list_decoding_bits as f64;
            out[3 * ci + 2] = cj.security_bits as f64;
        }
        for k in 0..3 {
            caps[k].push(out[k]);
            rbrs[k].push(out[3 + k]);
        }
        per_table.push((s.name, Bits { proven_udr: out[0], proven_ldr: out[1], conjectured: out[2] }));
    }
    // LogUp fingerprint: N = Σ interactions·height, W = widest message.
    let n: f64 = shapes.iter().map(|s| s.interactions as f64 * (1u64 << s.log_n) as f64).sum();
    let w = shapes.iter().map(|s| s.max_msg_width).max().unwrap_or(1);
    let lg = fingerprint_error(
        &LogUpAir { num_interactions: n.ceil() as usize, max_message_width: w },
        &InstanceShape {
            log_trace_length: 0,
            modulus_bits: EXT_BITS,
            collision_resistance: 512,
            num_batched_functions: 1,
        },
    )
    .0;
    let _ = caps;
    let tot = |v: &Vec<f64>| {
        let mut x = v.clone();
        x.push(lg);
        combine(&x)
    };
    let rbr = Bits { proven_udr: tot(&rbrs[0]), proven_ldr: tot(&rbrs[1]), conjectured: tot(&rbrs[2]) };
    // The SHA-256 collision cap applies once to the whole proof.
    let cap = |x: f64| x.min(128.0);
    Report {
        num_queries,
        query_pow,
        per_table,
        logup_bits: lg,
        total: Bits {
            proven_udr: cap(rbr.proven_udr),
            proven_ldr: cap(rbr.proven_ldr),
            conjectured: cap(rbr.conjectured),
        },
        total_rbr: rbr,
    }
}

/// Bits under the arena profile's FS accounting with q_H = 2^q_log2 hash
/// queries: -log2((q_H + 1)·ε_rbr + q_H² / 2^256).
pub fn profile_bits(rbr_bits: f64, q_log2: f64) -> f64 {
    let a = (q_log2 - rbr_bits).exp2();
    let b = (2.0 * q_log2 - 256.0).exp2();
    -(a + b).log2()
}

pub fn default_shapes_for_heights(heights_log: &[usize]) -> Vec<TableShape> {
    table_shapes(heights_log)
}

pub fn airs() -> Vec<NpAir> {
    all_airs()
}
