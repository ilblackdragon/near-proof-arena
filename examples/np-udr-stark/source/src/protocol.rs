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
use crate::field::{read_ef, read_f, put_ef, put_f, EF, F};
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
    pub batch_bits: Vec<usize>,
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
            if tab.width == 0 {
                return Err(format!("table {t}: zero width"));
            }
        }
        let hmax = *heights.iter().max().unwrap();
        if hmax < 2 {
            return Err("largest table must have at least 4 rows".into());
        }
        let l0 = hmax + LOG_BLOWUP;
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
        loop {
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
        let batch_bits = batch_len.iter().map(|&m| ceil_log2(m)).collect();
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
            batch_bits,
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
    pub version: u32,
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

fn put_u32(b: &mut Vec<u8>, x: usize) {
    b.extend_from_slice(&(x as u32).to_le_bytes());
}

fn put_opening(b: &mut Vec<u8>, o: &Opening) {
    put_u32(b, o.rows.len());
    for r in &o.rows {
        put_u32(b, r.len());
        for x in r {
            put_f(b, *x);
        }
    }
    put_u32(b, o.siblings.len());
    for s in &o.siblings {
        b.extend_from_slice(s);
    }
}

impl Proof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut b = vec![];
        put_u32(&mut b, self.version as usize);
        put_u32(&mut b, self.heights.len());
        b.extend(self.heights.iter().map(|&h| h as u8));
        b.extend_from_slice(&self.root_main);
        b.extend_from_slice(&self.root_aux);
        put_u32(&mut b, self.aux_finals.len());
        for x in &self.aux_finals {
            put_ef(&mut b, *x);
        }
        b.extend_from_slice(&self.root_quot);
        put_u32(&mut b, self.ood.len());
        for x in &self.ood {
            put_ef(&mut b, *x);
        }
        put_u32(&mut b, self.fri_roots.len());
        for r in &self.fri_roots {
            b.extend_from_slice(r);
        }
        put_ef(&mut b, self.final_poly[0]);
        put_ef(&mut b, self.final_poly[1]);
        put_opening(&mut b, &self.open_main);
        put_opening(&mut b, &self.open_aux);
        put_opening(&mut b, &self.open_quot);
        for o in &self.open_fri {
            put_opening(&mut b, o);
        }
        b
    }

    /// Context-free parse. Rejects oversize input, non-canonical field
    /// elements, truncation and trailing bytes.
    pub fn from_bytes(b: &[u8]) -> Option<Proof> {
        if b.len() > MAX_PROOF_BYTES {
            return None;
        }
        let mut r = Reader { b, p: 0 };
        let version = r.u32()?;
        let nt = r.u32()? as usize;
        if nt > 255 {
            return None;
        }
        let heights = (0..nt).map(|_| r.u8().map(|x| x as usize)).collect::<Option<Vec<_>>>()?;
        let root_main = r.d64()?;
        let root_aux = r.d64()?;
        let aux_finals = r.vec(|r| r.ef())?;
        let root_quot = r.d64()?;
        let ood = r.vec(|r| r.ef())?;
        let fri_roots = r.vec(|r| r.d64())?;
        let final_poly = [r.ef()?, r.ef()?];
        let open_main = r.opening()?;
        let open_aux = r.opening()?;
        let open_quot = r.opening()?;
        let open_fri = (0..fri_roots.len()).map(|_| r.opening()).collect::<Option<Vec<_>>>()?;
        if r.p != b.len() {
            return None;
        }
        Some(Proof {
            heights,
            version,
            root_main,
            root_aux,
            aux_finals,
            root_quot,
            ood,
            fri_roots,
            final_poly,
            open_main,
            open_aux,
            open_quot,
            open_fri,
        })
    }
}

struct Reader<'a> {
    b: &'a [u8],
    p: usize,
}

impl Reader<'_> {
    fn take(&mut self, n: usize) -> Option<&[u8]> {
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
    fn d64(&mut self) -> Option<Digest64> {
        self.take(64).map(|s| s.try_into().unwrap())
    }
    fn f(&mut self) -> Option<F> {
        read_f(self.take(4)?)
    }
    fn ef(&mut self) -> Option<EF> {
        read_ef(self.take(32)?)
    }
    fn vec<T>(&mut self, mut g: impl FnMut(&mut Self) -> Option<T>) -> Option<Vec<T>> {
        let n = self.u32()? as usize;
        // every element takes at least 4 bytes: bound before allocating
        if n > (self.b.len() - self.p) / 4 {
            return None;
        }
        (0..n).map(|_| g(self)).collect()
    }
    fn opening(&mut self) -> Option<Opening> {
        let rows = self.vec(|r| r.vec(|r| r.f()))?;
        let siblings = self.vec(|r| r.d64())?;
        Some(Opening { rows, siblings })
    }
}
