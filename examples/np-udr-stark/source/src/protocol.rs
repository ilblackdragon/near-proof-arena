//! Shared protocol schedule (`np-udr-stark-v1`) and the proof wire format.
//!
//! # Domains
//! Table `t` has trace height `T_t = 2^{h_t}` (row `r` ↔ `ω_{T_t}^r`), LDE
//! size `n_t = 16·T_t`, `l_t = h_t + 4`. The largest LDE is `n0 = 2^{l0}`.
//! Table `t` is in *class* `k_t = l0 - l_t`; its LDE coset is
//! `s^{2^{k_t}}·⟨ω_{n_t}⟩` (`s = 31`). FRI layer `k` lives on
//! `s^{2^k}·⟨ω_{n0/2^k}⟩`; all evaluation vectors are stored in
//! bit-reversed order: position `j` of layer `k` is the point
//! `point(k, j) = s^{2^k}·ω_{l0-k}^{bitrev_{l0-k}(j)}`. Positions `2j, 2j+1`
//! are `±x`, and position `J` of layer 0 squares (k times) to position
//! `J >> k` of layer k.
//!
//! # Rounds (each challenge preceded by one absorbed message)
//! 1. msg `root_main`            → `α_fp`
//! 2. msg ε                      → `γ_mul`
//! 3. msg `root_aux ‖ finals`    → `α_c`
//! 4. msg `root_quot`            → `z` (decodeOod)
//! 5. msg `ood values`, then ε…  → batching challenges `r_{k,i}`, classes
//!    ascending, `i < ⌈log₂ m_k⌉`
//! 6. FRI, for layer `k = 0..L-1`: msg (`root_k` if `k` committed else ε) →
//!    `β_k`; then if `k+1` is a class layer: msg ε → `γ_{k+1}`
//! 7. msg `final poly` → `d_fin` → queries.
//!
//! # Proof bytes (all integers little-endian)
//! ```text
//! header   : u32 version=1, u32 numTables, u8 h_t × numTables
//! root_main: 64      root_aux: 64      u32 nFinals, K × nFinals
//! root_quot: 64
//! u32 nOod, K × nOod
//! u32 nFri, 64 × nFri
//! final    : K × 2   (p(y) = c0 + c1·y)
//! openings : main, aux, quot, fri_0 .. fri_{nFri-1}; each
//!            u32 nMats, per matrix (u32 nVals, F × nVals), u32 nSib, 64 × nSib
//! ```
//! The header bytes (version, numTables, heights) are also bound into `d_0`.

use crate::air::Air;
use crate::field::{put_ef, read_ef, read_f, EF, F};
use crate::hash::Digest64;
use crate::mmcs::Opening;

pub const VERSION: u32 = 1;
pub const LOG_BLOWUP: usize = 4;
pub const NUM_CHUNKS: usize = 24;
pub const PER_CHUNK: usize = 9;
pub const MAX_ARITY_LOG: usize = 3;
pub const MAX_PROOF_BYTES: usize = 8 << 20;
pub const MAX_LOG_LDE: usize = 26;

#[derive(Clone, Debug)]
pub struct Schedule {
    pub heights: Vec<usize>,
    pub l0: usize,
    /// class of each table
    pub class: Vec<usize>,
    /// number of FRI folds; final layer has size 32
    pub fri_l: usize,
    /// class layers (sorted, distinct), always contains 0
    pub class_layers: Vec<usize>,
    /// committed FRI layers and their log-arity
    pub committed: Vec<(usize, usize)>,
    /// main widths, aux widths (in K elements), quotient chunks
    pub w_main: Vec<usize>,
    pub w_aux: Vec<usize>,
    pub n_quot: Vec<usize>,
    /// number of DEEP terms per class layer (indexed like class_layers)
    pub batch_len: Vec<usize>,
    /// number of shared batching challenges `r_1..r_L`
    pub batch_rounds: usize,
    /// bus finals per table
    pub n_finals: Vec<usize>,
}

pub fn ceil_log2(m: usize) -> usize {
    if m <= 1 { 0 } else { (usize::BITS - (m - 1).leading_zeros()) as usize }
}

impl Schedule {
    pub fn new(air: &Air, heights: &[usize]) -> Result<Self, String> {
        if heights.len() != air.tables.len() {
            return Err("height count".into());
        }
        for (t, (&h, tab)) in heights.iter().zip(&air.tables).enumerate() {
            if h < 1 || h > tab.max_log {
                return Err(format!("table {t}: height 2^{h} out of range [2^1, 2^{}]", tab.max_log));
            }
        }
        let hmax = *heights.iter().max().unwrap();
        let l0 = hmax + LOG_BLOWUP;
        air.validate()?;
        if l0 > MAX_LOG_LDE {
            return Err("LDE too large".into());
        }
        let class: Vec<usize> = heights.iter().map(|&h| hmax - h).collect();
        let fri_l = hmax - 1;
        let mut class_layers = class.clone();
        class_layers.sort_unstable();
        class_layers.dedup();
        let mut committed = vec![];
        let mut k = 0;
        while fri_l > 0 {
            let next_class = class_layers.iter().copied().find(|&c| c > k).unwrap_or(usize::MAX);
            let next = (k + MAX_ARITY_LOG).min(next_class).min(fri_l);
            committed.push((k, next - k));
            if next == fri_l {
                break;
            }
            k = next;
        }
        let w_main: Vec<usize> = air.tables.iter().map(|t| t.width).collect();
        let w_aux: Vec<usize> = air.tables.iter().map(|t| t.aux_width()).collect();
        let n_quot: Vec<usize> = air.tables.iter().map(|t| t.num_quot_chunks()).collect();
        let batch_len: Vec<usize> = class_layers
            .iter()
            .map(|&c| {
                (0..heights.len())
                    .filter(|&t| class[t] == c)
                    .map(|t| 2 * w_main[t] + 2 * w_aux[t] + n_quot[t])
                    .sum()
            })
            .collect();
        // `batchRounds`: max(1, ⌈log₂ max(2, max class count)⌉)
        let batch_rounds = ceil_log2(batch_len.iter().copied().max().unwrap_or(0).max(2)).max(1);
        let n_finals: Vec<usize> = air.tables.iter().map(|t| t.num_finals()).collect();
        Ok(Schedule {
            heights: heights.to_vec(),
            l0,
            class,
            fri_l,
            class_layers,
            committed,
            w_main,
            w_aux,
            n_quot,
            batch_len,
            batch_rounds,
            n_finals,
        })
    }

    pub fn num_tables(&self) -> usize {
        self.heights.len()
    }
    pub fn log_lde(&self, t: usize) -> usize {
        self.heights[t] + LOG_BLOWUP
    }
    pub fn num_ood(&self) -> usize {
        (0..self.num_tables()).map(|t| self.ood_len(t)).sum()
    }
    pub fn ood_len(&self, t: usize) -> usize {
        2 * self.w_main[t] + 2 * self.w_aux[t] + self.n_quot[t]
    }
    /// Tables of class layer `c`, in table order.
    pub fn tables_of(&self, c: usize) -> Vec<usize> {
        (0..self.num_tables()).filter(|&t| self.class[t] == c).collect()
    }
    pub fn header_bytes(&self) -> Vec<u8> {
        let mut b = VERSION.to_le_bytes().to_vec();
        b.extend_from_slice(&(self.num_tables() as u32).to_le_bytes());
        b.extend(self.heights.iter().map(|&h| h as u8));
        b
    }
    /// Committed-layer index of layer `k`, if committed.
    pub fn committed_at(&self, k: usize) -> Option<usize> {
        self.committed.iter().position(|&(c, _)| c == k)
    }
}

/// `point(k, j) = s^{2^k} · ω_{l0-k}^{bitrev_{l0-k}(j)}`.
pub fn point(l0: usize, k: usize, j: usize) -> F {
    use p3_field::PrimeCharacteristicRing;
    let lg = l0 - k;
    crate::field::shift().exp_power_of_2(k) * crate::field::omega(lg).exp_u64(crate::mmcs::rev(j, lg) as u64)
}

/// Coefficient of term `i` of a class batch: `∏_j r_j^{bit_j(i)}`.
pub fn batch_coeffs(r: &[EF], m: usize) -> Vec<EF> {
    use p3_field::PrimeCharacteristicRing;
    (0..m)
        .map(|i| {
            let mut c = EF::ONE;
            for (j, rj) in r.iter().enumerate() {
                if (i >> j) & 1 == 1 {
                    c *= *rj;
                }
            }
            c
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq)]
pub struct Proof {
    pub heights: Vec<usize>,
    pub root_main: Digest64,
    pub root_aux: Digest64,
    pub aux_finals: Vec<EF>,
    pub root_quot: Digest64,
    pub ood: Vec<EF>,
    pub fri_roots: Vec<Digest64>,
    pub final_poly: [EF; 2],
    pub open_main: Opening,
    pub open_aux: Opening,
    pub open_quot: Opening,
    pub open_fri: Vec<Opening>,
}

/// Matrix shapes `(log, width in base elements)` of every oracle, in
/// schedule order (main, aux, quot, FRI layers), and the level-0 index
/// function of each tree (`x >> shift`).
pub fn oracle_shapes(sch: &Schedule) -> Vec<(Vec<(usize, usize)>, usize)> {
    let nt = sch.num_tables();
    let mut v = vec![
        ((0..nt).map(|t| (sch.log_lde(t), sch.w_main[t])).collect(), 0),
        ((0..nt).map(|t| (sch.log_lde(t), 8 * sch.w_aux[t])).collect(), 0),
        ((0..nt).map(|t| (sch.log_lde(t), 8 * sch.n_quot[t])).collect(), 0),
    ];
    for &(c, a) in &sch.committed {
        v.push((vec![(sch.l0 - c - a, 8 << a)], c + a));
    }
    v
}

impl Proof {
    pub fn openings(&self) -> Vec<&Opening> {
        let mut v = vec![&self.open_main, &self.open_aux, &self.open_quot];
        v.extend(self.open_fri.iter());
        v
    }

    /// Bytes of message 0..: header ‖ root_main.
    pub fn header_bytes(&self) -> Vec<u8> {
        let mut b = VERSION.to_le_bytes().to_vec();
        b.extend_from_slice(&(self.heights.len() as u32).to_le_bytes());
        b.extend(self.heights.iter().map(|&h| h as u8));
        b
    }

    /// FORMATS.md §5 (no length prefixes; `queries` are the layer-0 positions).
    pub fn to_bytes(&self, sch: &Schedule, queries: &[usize]) -> Vec<u8> {
        let mut b = self.header_bytes();
        b.extend_from_slice(&self.root_main);
        b.extend_from_slice(&self.root_aux);
        for x in &self.aux_finals {
            put_ef(&mut b, *x);
        }
        b.extend_from_slice(&self.root_quot);
        for x in &self.ood {
            put_ef(&mut b, *x);
        }
        for r in &self.fri_roots {
            b.extend_from_slice(r);
        }
        put_ef(&mut b, self.final_poly[0]);
        put_ef(&mut b, self.final_poly[1]);
        for ((shape, sh), op) in oracle_shapes(sch).iter().zip(self.openings()) {
            let idx: Vec<usize> = queries.iter().map(|&x| x >> sh).collect();
            crate::mmcs::write_opening(&mut b, shape, &idx, op);
        }
        b
    }
}

/// The commit-phase prefix of a proof, parsed with the schedule of its
/// header. Returns the proof without openings and the remaining bytes.
pub fn parse_prefix<'a>(air: &Air, b: &'a [u8]) -> Option<(Proof, Schedule, &'a [u8])> {
    if b.len() > MAX_PROOF_BYTES {
        return None;
    }
    let mut r = Reader { b, p: 0 };
    if r.u32()? != VERSION {
        return None;
    }
    let nt = r.u32()? as usize;
    if nt != air.tables.len() {
        return None;
    }
    let heights = (0..nt).map(|_| r.u8().map(|x| x as usize)).collect::<Option<Vec<_>>>()?;
    let sch = Schedule::new(air, &heights).ok()?;
    let root_main = r.d64()?;
    let root_aux = r.d64()?;
    let nf: usize = sch.n_finals.iter().sum();
    let aux_finals = (0..nf).map(|_| r.ef()).collect::<Option<Vec<_>>>()?;
    let root_quot = r.d64()?;
    let ood = (0..sch.num_ood()).map(|_| r.ef()).collect::<Option<Vec<_>>>()?;
    let fri_roots = (0..sch.committed.len()).map(|_| r.d64()).collect::<Option<Vec<_>>>()?;
    let final_poly = [r.ef()?, r.ef()?];
    let rest = &b[r.p..];
    let proof = Proof {
        heights,
        root_main,
        root_aux,
        aux_finals,
        root_quot,
        ood,
        fri_roots,
        final_poly,
        open_main: Opening::default(),
        open_aux: Opening::default(),
        open_quot: Opening::default(),
        open_fri: vec![],
    };
    Some((proof, sch, rest))
}

/// Parse the multiproofs (query phase) given the positions; requires that
/// no byte is left over.
pub fn parse_openings(proof: &mut Proof, sch: &Schedule, queries: &[usize], rest: &[u8]) -> Option<()> {
    let mut r = Reader { b: rest, p: 0 };
    let mut ops = vec![];
    for (shape, sh) in oracle_shapes(sch) {
        let idx: Vec<usize> = queries.iter().map(|&x| x >> sh).collect();
        ops.push(crate::mmcs::read_opening(&mut r, &shape, &idx)?);
    }
    if r.p != rest.len() {
        return None;
    }
    let mut it = ops.into_iter();
    proof.open_main = it.next()?;
    proof.open_aux = it.next()?;
    proof.open_quot = it.next()?;
    proof.open_fri = it.collect();
    Some(())
}

pub struct Reader<'a> {
    pub b: &'a [u8],
    pub p: usize,
}

impl Reader<'_> {
    pub fn take(&mut self, n: usize) -> Option<&[u8]> {
        if self.b.len() - self.p < n {
            return None;
        }
        let s = &self.b[self.p..self.p + n];
        self.p += n;
        Some(s)
    }
    fn u8(&mut self) -> Option<u8> {
        self.take(1).map(|s| s[0])
    }
    fn u32(&mut self) -> Option<u32> {
        self.take(4).map(|s| u32::from_le_bytes(s.try_into().unwrap()))
    }
    pub fn d64(&mut self) -> Option<Digest64> {
        self.take(64).map(|s| s.try_into().unwrap())
    }
    pub fn f(&mut self) -> Option<F> {
        read_f(self.take(4)?)
    }
    fn ef(&mut self) -> Option<EF> {
        read_ef(self.take(32)?)
    }
}
