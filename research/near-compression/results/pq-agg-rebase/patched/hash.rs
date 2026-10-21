//! NV hashing subsystem, word format v2 (air2 limbs).  Same job model as
//! `sha384/airs.rs` (framed messages `PREFIX || tag || units`), with:
//! * units: a canonical felt (4 LE bytes) or a whole 64-bit word (8 BE bytes, e.g. a
//!   digest/state word given as air2 limbs; it occupies two unit indices);
//! * words to the compression AIR as air2 limbs, interface messages as word pairs;
//! * framing, packing and block chaining live in the GLUE role (glue.rs).
use core::borrow::{Borrow, BorrowMut};

use openvm_recursion_circuit_derive::AlignedBorrow;
use openvm_stark_backend::{
    interaction::{BusIndex, InteractionBuilder, LookupBus, PermutationCheckBus},
    BaseAirWithPublicValues, PartitionedBaseAir,
};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_maybe_rayon::prelude::*;

use super::fmt::{limbs_from_bytes, split_bits, wl, NV_DIGEST};
use crate::sha384::{
    compress4_air::{Layout, ROWS},
    compress4_trace::{gen_main, gen_table, main_height, sha2_compress, Comp, SHA384_IV},
    config::{sha_levers, F},
};

#[derive(Clone, Copy, Debug)]
pub struct HashBuses {
    pub ctl: BusIndex,
    pub k: BusIndex,
    pub lb: BusIndex,
    pub iface: BusIndex,
    pub word: BusIndex,
    /// slot bus: units carry channel 1, transcript events channel 0
    pub slot: BusIndex,
    pub job: BusIndex,
    pub digest: BusIndex,
    pub byte: BusIndex,
}

pub const UNIT_FELT: u32 = 0;
pub const UNIT_WORD: u32 = 2;
/// kind of a 42-byte digest tail unit (top 2 bytes of word 5)
pub const UNIT_HALF: u32 = 3;
/// job-bus tag of Merkle node jobs (outside the byte range of prefix-job tags)
pub const NODE_TAG: u32 = 256;

impl HashBuses {
    pub fn sha(&self) -> crate::sha384::compress2_air::Sha2Buses {
        crate::sha384::compress2_air::Sha2Buses {
            ctl: self.ctl,
            k: self.k,
            lb: self.lb,
            iface: self.iface,
        }
    }
    /// Producer: felt unit.
    pub fn send_felt<AB: InteractionBuilder>(
        &self,
        b: &mut AB,
        job: impl Into<AB::Expr>,
        idx: impl Into<AB::Expr>,
        v: impl Into<AB::Expr>,
        en: impl Into<AB::Expr>,
    ) {
        PermutationCheckBus::new(self.slot).send(
            b,
            [
                AB::Expr::ONE,
                job.into(),
                idx.into(),
                AB::Expr::from_u32(UNIT_FELT),
                v.into(),
                AB::Expr::ZERO,
                AB::Expr::ZERO,
            ],
            en,
        );
    }
    /// Producer: word unit (3 limbs), occupies unit indices idx, idx + 1.
    pub fn send_word<AB: InteractionBuilder>(
        &self,
        b: &mut AB,
        job: impl Into<AB::Expr>,
        idx: impl Into<AB::Expr>,
        l: [AB::Expr; 3],
        en: impl Into<AB::Expr>,
    ) {
        let [l0, l1, l2] = l;
        PermutationCheckBus::new(self.slot).send(
            b,
            [
                AB::Expr::ONE,
                job.into(),
                idx.into(),
                AB::Expr::from_u32(UNIT_WORD),
                l0,
                l1,
                l2,
            ],
            en,
        );
    }
    pub fn send_job<AB: InteractionBuilder>(
        &self,
        b: &mut AB,
        job: impl Into<AB::Expr>,
        tag: impl Into<AB::Expr>,
        en: impl Into<AB::Expr>,
    ) {
        self.send_job_tr(b, job, tag, AB::Expr::ZERO, en);
    }
    /// Job start (job, tag, tr): tr = 1 for Merkle jobs (leaf / node; truncated 42-byte digest).
    pub fn send_job_tr<AB: InteractionBuilder>(
        &self,
        b: &mut AB,
        job: impl Into<AB::Expr>,
        tag: impl Into<AB::Expr>,
        tr: impl Into<AB::Expr>,
        en: impl Into<AB::Expr>,
    ) {
        PermutationCheckBus::new(self.job).send(b, [job.into(), tag.into(), tr.into()], en);
    }
    /// Consumer: digest pair j (words 2j, 2j+1 as 6 limbs) of `job`.
    pub fn receive_digest_pair<AB: InteractionBuilder>(
        &self,
        b: &mut AB,
        job: impl Into<AB::Expr>,
        j: usize,
        limbs: &[AB::Expr],
        en: impl Into<AB::Expr>,
    ) {
        assert_eq!(limbs.len(), 6);
        let msg: Vec<AB::Expr> = [job.into(), AB::Expr::from_usize(j)]
            .into_iter()
            .chain(limbs.iter().cloned())
            .collect();
        PermutationCheckBus::new(self.digest).receive(b, msg, en);
    }
    /// Consumer: the 18-limb digest of `job` (3 pairs).
    pub fn receive_digest<AB: InteractionBuilder>(
        &self,
        b: &mut AB,
        job: impl Into<AB::Expr>,
        limbs: &[AB::Expr],
        en: impl Into<AB::Expr>,
    ) {
        let (job, en): (AB::Expr, AB::Expr) = (job.into(), en.into());
        for j in 0..3 {
            self.receive_digest_pair(b, job.clone(), j, &limbs[6 * j..6 * j + 6], en.clone());
        }
    }
}

pub fn iv_limbs18() -> [u32; 24] {
    std::array::from_fn(|i| wl(SHA384_IV[i / 3])[i % 3])
}

/// Byte-pair table: one row per (x, y) in [0, 256)^2 (x fastest); the byte bus carries
/// pairs (x, y); a single byte v is looked up as (v, 0).
/// Columns: x, y, z = [x = 255], inv = (x - 255)^-1 (0 if x = 255), multiplicity.
#[derive(Clone, Copy, Debug)]
pub struct ByteAir {
    pub buses: HashBuses,
}
pub const BYTE_W: usize = 5;
impl<T> BaseAir<T> for ByteAir {
    fn width(&self) -> usize {
        BYTE_W
    }
}
impl<T> BaseAirWithPublicValues<T> for ByteAir {}
impl<T> PartitionedBaseAir<T> for ByteAir {}
impl<AB: AirBuilder + InteractionBuilder> Air<AB> for ByteAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let (local, next) = (main.row_slice(0).unwrap(), main.row_slice(1).unwrap());
        let (x, y, z, inv) = (local[0], local[1], local[2], local[3]);
        let one = AB::Expr::ONE;
        let top = AB::Expr::from_u32(255);
        builder.assert_bool(z);
        builder.assert_zero(z * (x - top.clone()));
        builder.assert_eq((x - top.clone()) * inv, one.clone() - z);
        builder.when_first_row().assert_zero(x);
        builder.when_first_row().assert_zero(y);
        builder.when_transition().assert_eq(next[0], (x + one.clone()) * (one.clone() - z));
        builder.when_transition().assert_eq(next[1], y + z);
        builder.when_last_row().assert_eq(x, top.clone());
        builder.when_last_row().assert_eq(y, top);
        LookupBus::new(self.buses.byte).add_key_with_lookups(builder, [x, y], local[4]);
    }
}

/// Byte-pair lookup (both entries must be bytes).
pub fn lookup_pair<AB: InteractionBuilder>(b: &mut AB, bus: BusIndex, x: impl Into<AB::Expr>, y: impl Into<AB::Expr>, en: impl Into<AB::Expr>) {
    LookupBus::new(bus).lookup_key(b, [x.into(), y.into()], en);
}
/// Single byte lookup, as the pair (v, 0).
pub fn lookup_byte<AB: InteractionBuilder>(b: &mut AB, bus: BusIndex, v: impl Into<AB::Expr>, en: impl Into<AB::Expr>) {
    LookupBus::new(bus).lookup_key(b, [v.into(), AB::Expr::ZERO], en);
}
/// Count a pair lookup in the 65536-entry table counts.
#[inline]
pub fn cnt2(counts: &mut [u32], x: usize, y: usize) {
    counts[x + 256 * y] += 1;
}
pub const BYTE_TABLE: usize = 1 << 16;

// ---------------------------------------------------------------------------------------
// Trace generation
// ---------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum U2 {
    Felt(u32),
    Word(u64),
    /// the top 2 bytes of a word (tail of a 42-byte digest); occupies 2 unit indices and is
    /// carried as a word unit whose low 6 bytes are zero
    Half(u64),
}
impl U2 {
    pub fn nunits(self) -> usize {
        match self {
            U2::Felt(_) => 1,
            U2::Word(_) | U2::Half(_) => 2,
        }
    }
    pub fn bytes(self) -> Vec<u8> {
        match self {
            U2::Felt(x) => x.to_le_bytes().to_vec(),
            U2::Word(w) => w.to_be_bytes().to_vec(),
            U2::Half(w) => w.to_be_bytes()[..2].to_vec(),
        }
    }
}
/// A digest as word units: 6 words (48 B) or 5 words + a 2-byte tail (42 B).
pub fn digest_units(words: [u64; 6]) -> Vec<U2> {
    let mut v: Vec<U2> = words[..5].iter().map(|&w| U2::Word(w)).collect();
    v.push(if crate::sha384::config::sha_levers().digest_bytes == 42 { U2::Half(words[5]) } else { U2::Word(words[5]) });
    v
}

#[derive(Clone, Debug)]
pub struct Job2 {
    /// job id (unit / digest key)
    pub id: u32,
    /// Merkle node job: message NODE_WORD || 12 word units (no prefix / tag / lengths)
    pub node: bool,
    pub tag: u8,
    pub units: Vec<U2>,
    /// transcript blocks: output words read by the sample role (bit w = word w); GLUE sends
    /// each such word once more on the digest bus
    pub wread: u8,
}
impl Job2 {
    pub fn message(&self) -> Vec<u8> {
        if self.node {
            let mut m = sha_levers().node_prefix().to_vec();
            for u in &self.units {
                assert!(matches!(u, U2::Word(_) | U2::Half(_)));
                m.extend(u.bytes());
            }
            assert_eq!(m.len(), 8 + 2 * sha_levers().digest_bytes);
            return m;
        }
        let mut m = sha_levers().prefix().to_vec();
        m.push(self.tag);
        for u in &self.units {
            m.extend(u.bytes());
        }
        m
    }
    pub fn num_blocks(&self) -> usize {
        (self.message().len() + 17).div_ceil(128)
    }
}

pub fn sha384_blocks(msg: &[u8]) -> (Vec<Comp>, [u64; 6]) {
    let blocks = crate::sha384::compress2_trace::pad_message(msg);
    let mut h = SHA384_IV;
    let mut comps = Vec::with_capacity(blocks.len());
    for b in blocks {
        let c = Comp { h, block: b };
        h = sha2_compress(&c);
        comps.push(c);
    }
    (comps, std::array::from_fn(|i| h[i]))
}

#[derive(Default)]
pub struct Work2 {
    pub jobs: Vec<Job2>,
    /// direct compressions (Merkle nodes): compression ids 0..nodes.len()
    pub nodes: Vec<Comp>,
}

pub struct Traces2 {
    pub compress: RowMajorMatrix<F>,
    pub table: RowMajorMatrix<F>,
    /// GLUE rows (pair rows, see glue.rs), GLUE_W wide, unpadded
    pub glue_rows: Vec<[F; super::glue::GLUE_W]>,
    pub byte_counts: Vec<u32>,
    pub job_digests: Vec<[u64; 6]>,
    pub n_compressions: usize,
}

fn to_f(v: Vec<u32>, width: usize) -> RowMajorMatrix<F> {
    RowMajorMatrix::new(v.into_par_iter().map(F::from_u32).collect(), width)
}

/// Compression trace (node compressions first, then the job blocks) and the GLUE rows.
pub fn generate2(work: &Work2, lay: Layout, min_compress_h: Option<usize>) -> Traces2 {
    let job_blocks: Vec<(Vec<Comp>, [u64; 6])> = work
        .jobs
        .par_iter()
        .map(|j| sha384_blocks(&j.message()))
        .collect();
    let mut comps = work.nodes.clone();
    comps.extend(job_blocks.iter().flat_map(|b| b.0.iter().copied()));
    let ch = main_height(comps.len()).max(min_compress_h.unwrap_or(1));
    let main = gen_main(&comps, ch);
    let table = gen_table(&main, ch);
    let mut byte_counts = vec![0u32; BYTE_TABLE];
    let glue_rows = super::glue::glue_rows(&work.jobs, &job_blocks, work.nodes.len(), &mut byte_counts);
    Traces2 {
        compress: to_f(main, lay.width),
        table: to_f(table, crate::sha384::compress4_air::T_WIDTH),
        glue_rows,
        byte_counts,
        job_digests: job_blocks.iter().map(|b| b.1).collect(),
        n_compressions: comps.len(),
    }
}

pub fn byte_table2(counts: &[u32]) -> RowMajorMatrix<F> {
    assert_eq!(counts.len(), BYTE_TABLE);
    let mut v = F::zero_vec(BYTE_TABLE * BYTE_W);
    let inv255 = |x: usize| {
        let d = F::from_usize(x) - F::from_u32(255);
        if d == F::ZERO { F::ZERO } else { d.inverse() }
    };
    for r in 0..BYTE_TABLE {
        let (x, y) = (r % 256, r / 256);
        let row = &mut v[r * BYTE_W..(r + 1) * BYTE_W];
        row[0] = F::from_usize(x);
        row[1] = F::from_usize(y);
        row[2] = F::from_bool(x == 255);
        row[3] = inv255(x);
        row[4] = F::from_u32(counts[r]);
    }
    RowMajorMatrix::new(v, BYTE_W)
}

#[allow(dead_code)]
fn _w(m: &RowMajorMatrix<F>) -> usize {
    m.width()
}
