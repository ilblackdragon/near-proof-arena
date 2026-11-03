//! E2E M4: a Wasm call cut into segments (`WasmBase/SegAir.lean`, `wasmBaseSegAir`).
//!
//! The whole call is traced once by `tracegen::generate_cuts` at `wasmBaseM2Air` with cut points;
//! at every cut the generator records the machine (`CutSnap`) and then resets every live message's
//! producer time to the cut and relabels activation ids to depths, so the rows after the cut are
//! exactly the rows the next segment proves.  This module builds, per segment:
//!
//! * the instruction / host / register rows with `ts` in `(t_in, t_out]` (copied by name);
//! * `SEGB` (boundary), `CUTI`/`CUTO` (the small-state stream, SHA-384), `MEMB` (touched 1 KiB
//!   blocks), `MPATH` (old and new Merkle paths), `DROP` (tombstones, dead locals), the HOST gas
//!   register columns;
//! * the lookup multiplicities (RANGE16, BYTE, CODE, FUNC, HOSTT), recounted from the rows;
//! * the SHA-512 compressions every hashing row consumes (the native chip's input).
//!
//! The seg AIR may also be `wasmBaseSegAirMP` (`WasmBase/SegAirMP.lean`, E2E M4b; detected by an
//! `idx` column in MPATH): MPATH is then the batched Merkle multiproof, one row per touched tree
//! node (`multiproof_rows`), and SEGB's `nbt` is 1 (a root row) or 0.
//!
//! E2E M4c: `wasmBaseSegAirG` (`WasmBase/SegAirG.lean`, detected by a `SEGG` table; the full run is
//! then traced at `wasmBaseM3Air`): MEMG rows are copied, a block grown in the segment is a MEMBG
//! block (zero bytes produced at the grow's time, old leaf = the zero leaf), an old block above
//! 64 MiB a MEMBH block, SEGG carries the size message across the cut and, when the depth grows
//! (16 -> 17), is the root of the lifted tree (`Tree::lift`, `LiftRoot`).
use crate::air::{AirSpec, TableSpec};
use crate::s384::reference::{Comp, SHA384_IV, sha2_compress};
use crate::tracegen::{CutSnap, Gen, Live, Prep, image_byte, limbs};
use p3_baby_bear::BabyBear as F;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use std::collections::{BTreeMap, HashMap};

pub const P: u64 = 2013265921;

fn fe(x: u64) -> F {
    F::from_u64(x)
}
/// The SHA-512 chip's limbs of a 64-bit word.
pub fn wl(x: u64) -> [u64; 3] {
    [x & ((1 << 21) - 1), (x >> 21) & ((1 << 21) - 1), x >> 42]
}

// public value layout (`Seg.pub*` in SegAir.lean)
pub const PUB_STATUS: usize = 8;
pub const PUB_MEM: usize = 9;
pub const PUB_PC_IN: usize = 11;
pub const PUB_T_IN: usize = 12;
pub const PUB_S_IN: usize = 13;
pub const PUB_SB_IN: usize = 14;
pub const PUB_CID_IN: usize = 15;
pub const PUB_SSEG_IN: usize = 16;
pub const PUB_GB_IN: usize = 17;
pub const PUB_PC_OUT: usize = 21;
pub const PUB_T_OUT: usize = 22;
pub const PUB_S_OUT: usize = 23;
pub const PUB_SB_OUT: usize = 24;
pub const PUB_CID_OUT: usize = 25;
pub const PUB_SSEG_OUT: usize = 26;
pub const PUB_GB_OUT: usize = 27;
pub const PUB_CTX_IN: usize = 31;
pub const PUB_CTX_OUT: usize = 49;
pub const PUB_MEM_IN: usize = 67;
pub const PUB_MEM_OUT: usize = 85;
pub const PUB_DEPTH: usize = 103;
pub const PUB_NBLK: usize = 104;
pub const NUM_PUB: usize = 105;
// `wasmBaseSegAirG` (`WasmBase/SegAirG.lean`, E2E M4c): pub 103 is `D_out`, 104 `min(nblk_in, 2^16)`
pub const PUB_NBLK_IN: usize = 105;
pub const PUB_NBLK_OUT: usize = 106;
pub const PUB_DEPTH_IN: usize = 107;
pub const NUM_PUB_G: usize = 108;

/// The boundary a segment starts or ends at (the public values' content).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bnd {
    pub pc: u64,
    pub t: u64,
    pub s: u64,
    pub sb: u64,
    /// the top frame's depth (the relabelled activation id)
    pub cid: u64,
    pub sseg: u64,
    pub segb: u64,
    pub ctx: [u64; 6],
    pub mem: [u64; 6],
    /// the memory geometry (`nblk = 64·pages`, `D = memDepth`)
    pub nblk: u64,
    pub depth: u64,
}

/// `WasmView.memDepth`: `bitlen (max nblk 2 − 1)`.
pub fn depth_of(nblk: u64) -> usize {
    (usize::BITS - ((nblk as usize).max(2) - 1).leading_zeros()) as usize
}

/// The zero-subtree roots `Z_0 = sha384 0¹⁰²⁴`, `Z_{k+1} = H(Z_k ‖ Z_k)` (`Seg.Grow.zrootW`).
pub fn zero_roots(n: usize) -> Vec<[u64; 6]> {
    let mut z = vec![leaf_hash(&[0u64; 1024])];
    for k in 0..n {
        let x = node_hash(&z[k], &z[k]);
        z.push(x);
    }
    z
}

// ------------------------------------------------------------------------------------------
// SHA-512 compressions
// ------------------------------------------------------------------------------------------

#[derive(Default)]
pub struct Sha {
    pub comps: Vec<Comp>,
}
impl Sha {
    /// Register a compression for the chip; returns its interface id `cid = 128·index` and output.
    pub fn comp(&mut self, h: [u64; 8], block: [u64; 16]) -> (u64, [u64; 8]) {
        let c = Comp { h, block };
        let out = sha2_compress(&c);
        let cid = (self.comps.len() * 128) as u64;
        self.comps.push(c);
        (cid, out)
    }
}
fn compress(h: [u64; 8], block: [u64; 16]) -> [u64; 8] {
    sha2_compress(&Comp { h, block })
}
fn d6(h: &[u64; 8]) -> [u64; 6] {
    [h[0], h[1], h[2], h[3], h[4], h[5]]
}
fn limbs24(h: &[u64; 8]) -> Vec<u64> {
    h.iter().flat_map(|&w| wl(w)).collect()
}
fn limbs18(h: &[u64; 6]) -> Vec<u64> {
    h.iter().flat_map(|&w| wl(w)).collect()
}

/// The 16 big-endian words of 128 bytes.
fn be_words(b: &[u64]) -> [u64; 16] {
    std::array::from_fn(|w| (0..8).fold(0u64, |acc, i| (acc << 8) | b[8 * w + i]))
}
/// SHA-384 padding block of a message of `bits` bits that is a whole number of blocks.
fn pad_block(bits: u64) -> [u64; 16] {
    let mut b = [0u64; 16];
    b[0] = 1 << 63;
    b[15] = bits;
    b
}
/// SHA-384 of a 1 KiB block (the Merkle leaf), natively.
pub fn leaf_hash(bytes: &[u64]) -> [u64; 6] {
    let mut h = SHA384_IV;
    for k in 0..8 {
        h = compress(h, be_words(&bytes[128 * k..128 * (k + 1)]));
    }
    d6(&compress(h, pad_block(8192)))
}
fn node_block(l: &[u64; 6], r: &[u64; 6]) -> [u64; 16] {
    let mut b = [0u64; 16];
    b[..6].copy_from_slice(l);
    b[6..12].copy_from_slice(r);
    b[12] = 1 << 63;
    b[15] = 768;
    b
}
pub fn node_hash(l: &[u64; 6], r: &[u64; 6]) -> [u64; 6] {
    d6(&compress(SHA384_IV, node_block(l, r)))
}

// ------------------------------------------------------------------------------------------
// The canonical boundary stream
// ------------------------------------------------------------------------------------------

/// The canonical (relabelled, sorted) messages of a cut, with their raw form.
pub fn canon(s: &CutSnap) -> Vec<([u64; 7], Live)> {
    let d = |c: u64| s.depth_of.iter().find(|x| x.0 == c).map(|x| x.1).unwrap_or_else(|| panic!("cid {c} not live"));
    let mut out: Vec<([u64; 7], Live)> = s
        .live
        .iter()
        .map(|l| {
            let e = match l.space {
                4 => [4, d(l.slot), l.tag, l.v[0], l.v[1], d(l.v[2]), l.v[3]],
                sp if sp >= 16 => [16 + d(sp - 16), l.slot, l.tag, l.v[0], l.v[1], l.v[2], l.v[3]],
                _ => [l.space, l.slot, l.tag, l.v[0], l.v[1], l.v[2], l.v[3]],
            };
            (e, *l)
        })
        .collect();
    out.sort_by_key(|(e, _)| (e[0], e[1]));
    for w in out.windows(2) {
        assert!((w[0].0[0], w[0].0[1]) < (w[1].0[0], w[1].0[1]), "duplicate boundary key {:?}", w[0].0);
    }
    for (e, _) in out.iter() {
        for &f in e.iter() {
            assert!(f < 1 << 30, "boundary field {f} >= 2^30 (domain)");
        }
    }
    out
}

/// The 8 words of one canonical message (`lo + 2^21·hi + 2^42·mark`, then a zero word).
fn msg_words(e: Option<&[u64; 7]>) -> [u64; 8] {
    let mut w = [0u64; 8];
    if let Some(e) = e {
        for k in 0..7 {
            w[k] = (e[k] & 0xffff) | ((e[k] >> 16) << 21) | (((k == 0) as u64) << 42);
        }
    }
    w
}

/// The digest of a canonical stream (natively, no chip).
pub fn stream_digest(es: &[[u64; 7]]) -> [u64; 6] {
    let mut h = SHA384_IV;
    let ng = es.len().div_ceil(2);
    for g in 0..ng {
        let a = msg_words(es.get(2 * g));
        let b = msg_words(es.get(2 * g + 1));
        let mut blk = [0u64; 16];
        blk[..8].copy_from_slice(&a);
        blk[8..].copy_from_slice(&b);
        h = compress(h, blk);
    }
    d6(&compress(h, pad_block(1024 * ng as u64)))
}

// ------------------------------------------------------------------------------------------
// The memory Merkle tree
// ------------------------------------------------------------------------------------------

pub struct Tree {
    pub d: usize,
    pub lv: Vec<Vec<[u64; 6]>>,
}
impl Tree {
    /// The tree over `nblk` blocks of the call's initial memory (leaves `≥ nblk` hash a zero block).
    pub fn initial(prep: &Prep) -> Tree {
        let nblk = (prep.mem >> 10) as usize;
        let d = (usize::BITS - (nblk.max(2) - 1).leading_zeros()) as usize;
        let zero = leaf_hash(&[0u64; 1024]);
        let mut leaves = vec![zero; 1 << d];
        for (b, leaf) in leaves.iter_mut().enumerate().take(nblk) {
            let base = (b as u64) << 10;
            if base >= prep.data_end {
                continue;
            }
            let bytes: Vec<u64> = (0..1024).map(|i| image_byte(prep, base + i)).collect();
            *leaf = leaf_hash(&bytes);
        }
        let mut lv = vec![leaves];
        for l in 0..d {
            let prev = &lv[l];
            let next: Vec<[u64; 6]> = (0..prev.len() / 2).map(|i| node_hash(&prev[2 * i], &prev[2 * i + 1])).collect();
            lv.push(next);
        }
        Tree { d, lv }
    }
    pub fn root(&self) -> [u64; 6] {
        self.lv[self.d][0]
    }
    /// E2E M4c: one more level; the old tree is the left subtree, the right one is all-zero.
    pub fn lift(&mut self) {
        let z = zero_roots(self.d);
        for l in 0..=self.d {
            let n = self.lv[l].len();
            self.lv[l].extend(std::iter::repeat_n(z[l], n));
        }
        let r = node_hash(&self.lv[self.d][0], &self.lv[self.d][1]);
        self.lv.push(vec![r]);
        self.d += 1;
    }
}

// ------------------------------------------------------------------------------------------
// Row builder by column name
// ------------------------------------------------------------------------------------------

pub struct Tb<'a> {
    pub spec: &'a TableSpec,
    idx: HashMap<String, usize>,
    pub rows: Vec<Vec<F>>,
}
impl<'a> Tb<'a> {
    pub fn new(spec: &'a TableSpec) -> Self {
        let idx = spec.cols.iter().enumerate().map(|(i, c)| (c.clone(), i)).collect();
        Tb { spec, idx, rows: vec![] }
    }
    pub fn push(&mut self) {
        self.rows.push(vec![F::ZERO; self.spec.cols.len()]);
    }
    pub fn s(&mut self, name: &str, v: F) {
        let i = *self.idx.get(name).unwrap_or_else(|| panic!("{}: no col {name}", self.spec.name));
        *self.rows.last_mut().unwrap().get_mut(i).unwrap() = v;
    }
    pub fn u(&mut self, name: &str, v: u64) {
        self.s(name, fe(v));
    }
    pub fn col(&self, name: &str) -> usize {
        self.idx[name]
    }
    /// Pad to a power of two (`≥ 4`, `+ extra` rows at least) with `pad` rows.
    pub fn finish(mut self, extra: usize, pad: &[(&str, u64)]) -> RowMajorMatrix<F> {
        let h = (self.rows.len() + extra).max(4).next_power_of_two();
        while self.rows.len() < h {
            self.push();
            for &(n, v) in pad {
                self.u(n, v);
            }
        }
        let w = self.spec.cols.len();
        RowMajorMatrix::new(self.rows.into_iter().flatten().collect(), w)
    }
}

// ------------------------------------------------------------------------------------------
// The stream tables CUTI / CUTO
// ------------------------------------------------------------------------------------------

/// Fill a stream table: data groups, one padding group, dead rows.  `raw` is `Some` for `CUTO`.
/// Returns the digest.
fn stream_rows(tb: &mut Tb, sha: &mut Sha, es: &[([u64; 7], Live)], out: bool, lookups: &HashMap<u64, u64>) -> [u64; 6] {
    let ng = es.len().div_ceil(2);
    let mut h = SHA384_IV;
    let mut dep = 0u64;
    let mut gi = 0u64;
    let k4 = |e: &([u64; 7], Live)| e.1.space == 4;
    for g in 0..=ng {
        let pad = g == ng;
        let (blk, words): ([u64; 16], [[u64; 8]; 2]) = if pad {
            let b = pad_block(1024 * ng as u64);
            (b, [b[..8].try_into().unwrap(), b[8..].try_into().unwrap()])
        } else {
            let a = msg_words(es.get(2 * g).map(|x| &x.0));
            let b = msg_words(es.get(2 * g + 1).map(|x| &x.0));
            let mut blk = [0u64; 16];
            blk[..8].copy_from_slice(&a);
            blk[8..].copy_from_slice(&b);
            (blk, [a, b])
        };
        let _ = words;
        let h_in = h;
        let (cid, h_out) = sha.comp(h, blk);
        h = h_out;
        for j in 0..2usize {
            tb.push();
            tb.u("j", j as u64);
            tb.u("cid", cid);
            let hh = if j == 0 { &h_in } else { &h_out };
            for (i, l) in limbs24(hh).into_iter().enumerate() {
                tb.u(&format!("h{i}"), l);
            }
            if pad {
                tb.u("kP", 1);
                tb.u("gi", gi);
                if j == 1 {
                    tb.u("gl", gi & 2047);
                    tb.u("gh", gi >> 11);
                }
            } else {
                tb.u("kD", 1);
                tb.u("gi", gi);
                if let Some(m) = es.get(2 * g + j) {
                    tb.u("act", 1);
                    for k in 0..7 {
                        tb.u(&format!("lo{k}"), m.0[k] & 0xffff);
                        tb.u(&format!("hi{k}"), m.0[k] >> 16);
                    }
                    if out {
                        let r = &m.1;
                        tb.u("space", r.space);
                        tb.u("slot", r.slot);
                        tb.u("x2", r.v[2]);
                        tb.u("tp", r.tp);
                        let cls = match r.space {
                            0 => "k0",
                            2 => "k2",
                            4 => "k4",
                            5 => "k5",
                            6 => "k6",
                            sp if sp >= 16 => "kL",
                            sp => panic!("space {sp} in the boundary stream"),
                        };
                        tb.u(cls, 1);
                        if r.space >= 16 {
                            let c = r.space - 16;
                            tb.u("clo", c & 0xffff);
                            tb.u("chi", c >> 16);
                        }
                        if k4(m) {
                            dep += 1;
                            tb.u("mm", *lookups.get(&r.slot).unwrap_or(&0));
                        }
                        let ix = 2 * g + j;
                        if let Some(nx) = es.get(ix + 1) {
                            let same = nx.0[0] == m.0[0];
                            let d = if same { nx.0[1] - m.0[1] - 1 } else { nx.0[0] - m.0[0] - 1 };
                            assert!(d < 1 << 29);
                            tb.u("same", same as u64);
                            tb.u("dlo", d & 0xffff);
                            tb.u("dhi", d >> 16);
                            if k4(m) && k4(nx) {
                                let d = nx.1.slot - r.slot - 1;
                                assert!(d < 1 << 28, "records not in increasing activation order");
                                tb.u("rlo", d & 0xffff);
                                tb.u("rhi", d >> 16);
                            }
                        }
                    }
                }
            }
            if out {
                tb.u("dep", dep);
            }
        }
        if !pad {
            gi += 1;
        }
    }
    d6(&h)
}

fn finish_stream(mut tb: Tb, out: bool, dep: u64) -> RowMajorMatrix<F> {
    let h = tb.rows.len().max(4).next_power_of_two();
    while tb.rows.len() < h {
        tb.push();
        tb.u("kX", 1);
        if out {
            tb.u("dep", dep);
        }
    }
    let w = tb.spec.cols.len();
    RowMajorMatrix::new(tb.rows.into_iter().flatten().collect(), w)
}

// ------------------------------------------------------------------------------------------
// One segment
// ------------------------------------------------------------------------------------------

pub struct SegStats {
    pub blocks: usize,
    pub blocks_ro: usize,
    pub stream_in: usize,
    pub stream_out: usize,
    pub drops: usize,
    pub tombs: usize,
    pub comps: usize,
    pub comps_stream: usize,
    pub comps_memb: usize,
    pub comps_mpath: usize,
    /// E2E M4c: pages at the segment's start / end, blocks grown in it (MEMBG), old blocks above
    /// 64 MiB (MEMBH), whether the tree depth increased (SEGG's lift root)
    pub pages: (u64, u64),
    pub grown: usize,
    pub high: usize,
    pub lift: bool,
}

pub struct SegInst {
    pub mats: Vec<RowMajorMatrix<F>>,
    pub pubs: Vec<F>,
    pub comps: Vec<Comp>,
    pub b_in: Bnd,
    pub b_out: Bnd,
    pub halted: u64,
    pub stats: SegStats,
}

/// Rows of the full-run matrix `m` (table `spec`) whose `key` column lies in `(lo, hi]`.
fn rows_in(spec: &TableSpec, m: &RowMajorMatrix<F>, key: &str, lo: u64, hi: u64) -> Vec<Vec<F>> {
    let w = spec.cols.len();
    let k = spec.col(key);
    m.values
        .chunks(w)
        .filter(|r| {
            let t = r[k].as_canonical_u32() as u64;
            t > lo && t <= hi
        })
        .map(|r| r.to_vec())
        .collect()
}

/// Build segment `k` (between `gen.cuts[k]` and `gen.cuts[k + 1]`).  `tree` is the memory tree at
/// the segment's start and is advanced to its end.
pub fn build(seg: &AirSpec, m2: &AirSpec, g: &Gen, prep: &Prep, k: usize, tree: &mut Tree) -> SegInst {
    let (c0, c1) = (&g.cuts[k], &g.cuts[k + 1]);
    let (t_in, t_out) = (c0.t, c1.t);
    let mut sha = Sha::default();
    let mut mats: Vec<Option<RowMajorMatrix<F>>> = vec![None; seg.tables.len()];
    let si = |n: &str| seg.index(n);
    let full = |n: &str| (&m2.tables[m2.index(n)], &g.mats[m2.index(n)]);

    // `wasmBaseSegAirG` (E2E M4c): MEMG, SEGG, MEMBG; the full run is then `wasmBaseM3Air`'s
    let grow_air = seg.tables.iter().any(|t| t.name == "SEGG");
    let (nblk_in, nblk_out) = (64 * c0.pages, 64 * c1.pages);
    if !grow_air {
        assert_eq!((nblk_in, nblk_out), (prep.mem >> 10, prep.mem >> 10), "memory.grow needs the segment AIR airSegG");
    }
    let mut names: Vec<&str> = vec!["ADD", "BIT", "MUL", "SHIFT", "CMP", "CONST", "STACK", "CTRL", "LOCAL", "DIV", "LOAD",
        "STORE", "CALL", "RET", "IF", "CONV", "UNREACH", "HOSTO", "HOSTB", "REG", "HOST"];
    if grow_air {
        names.push("MEMG");
    }

    // ---- copied rows -------------------------------------------------------------------------
    for name in names {
        let (fs, fm) = full(name);
        let key = if name == "HOSTO" { "q0" } else { "ts" };
        let rows = rows_in(fs, fm, key, t_in, t_out);
        let spec = &seg.tables[si(name)];
        let mut tb = Tb::new(spec);
        for r in rows {
            tb.push();
            for (ci, c) in fs.cols.iter().enumerate() {
                if spec.cols.iter().any(|x| x == c) {
                    tb.s(c, r[ci]);
                } else if !["atp", "ahp"].contains(&c.as_str()) {
                    // the full run is `wasmBaseM3Air` (HOST-W, REG-A): HOST-W's tag columns must be
                    // zero (all-i64 host signatures, = HOST'); REG-A's absent header is dropped
                    assert!(r[ci] == F::ZERO, "{name}.{c} = {} has no column in the segment AIR (i32 host signature)", r[ci]);
                }
            }
        }
        let (extra, pad): (usize, Vec<(&str, u64)>) = match name {
            "IF" => (1, vec![]),
            "HOSTB" => (1, vec![("f", 1)]),
            "REG" => (1, vec![("f", 1), ("kind", 1)]),
            _ => (0, vec![]),
        };
        if name == "HOST" {
            // the gas register: consumed `(S_seg, segb)` at its producer time, produced `(S + fee, g_after)`
            let mut g = c0.gas;
            g.2 = t_in;
            let (its, is_, ife) = (tb.col("ts"), tb.col("S"), tb.col("fee"));
            for r in tb.rows.iter_mut() {
                let ts = r[its].as_canonical_u32() as u64;
                let gl = limbs(g.1);
                let hi = (ts - g.2 - 1) >> 16;
                let names = ["gS", "gb0", "gb1", "gb2", "gb3", "gtp", "ghi"];
                let vals = [g.0, gl[0], gl[1], gl[2], gl[3], g.2, hi];
                for (n, v) in names.iter().zip(vals) {
                    r[spec.col(n)] = fe(v);
                }
                let ga: u64 = (0..4).map(|i| (r[spec.col(&format!("ga{i}"))].as_canonical_u32() as u64) << (16 * i)).sum();
                let s_after = r[is_].as_canonical_u32() as u64 + r[ife].as_canonical_u32() as u64;
                g = (s_after, ga, ts);
            }
            assert_eq!((g.0, g.1, g.2), (c1.gas.0, c1.gas.1, if c1.gas.2 <= t_in { t_in } else { c1.gas.2 }), "gas register at the cut");
        }
        let pads: Vec<(&str, u64)> = pad.clone();
        mats[si(name)] = Some(tb.finish(extra, &pads));
    }

    // ---- the boundary streams ------------------------------------------------------------------
    let ein = canon(c0);
    let eout = canon(c1);
    // CIDMAP lookups: locals and record callers of the out stream, and SEGB's final cid
    let mut lookups: HashMap<u64, u64> = HashMap::new();
    for (_, r) in eout.iter() {
        if r.space >= 16 {
            *lookups.entry(r.space - 16).or_default() += 1;
        }
        if r.space == 4 {
            *lookups.entry(r.v[2]).or_default() += 1;
        }
    }
    *lookups.entry(c1.cid).or_default() += 1;
    let mut cut_i = Tb::new(&seg.tables[si("CUTI")]);
    let ctx_in = stream_rows(&mut cut_i, &mut sha, &ein, false, &lookups);
    let mut cut_o = Tb::new(&seg.tables[si("CUTO")]);
    let ctx_out = stream_rows(&mut cut_o, &mut sha, &eout, true, &lookups);
    let comps_stream = sha.comps.len();
    let ndep = eout.iter().filter(|x| x.1.space == 4).count() as u64;
    mats[si("CUTI")] = Some(finish_stream(cut_i, false, 0));
    mats[si("CUTO")] = Some(finish_stream(cut_o, true, ndep));
    assert_eq!(ctx_in, stream_digest(&ein.iter().map(|x| x.0).collect::<Vec<_>>()));

    // ---- DROP ------------------------------------------------------------------------------------
    let mut drop = Tb::new(&seg.tables[si("DROP")]);
    for &c in c1.tombs.iter() {
        let n = c1.dead.iter().filter(|l| l.space == 16 + c).count() as u64;
        drop.push();
        drop.u("act", 1);
        drop.u("isT", 1);
        drop.u("c", c);
        drop.u("m", n);
    }
    for l in c1.dead.iter() {
        drop.push();
        drop.u("act", 1);
        drop.u("c", l.space - 16);
        drop.u("slot", l.slot);
        drop.u("tag", l.tag);
        for i in 0..4 {
            drop.u(&format!("x{i}"), l.v[i]);
        }
        drop.u("tp", l.tp);
    }
    mats[si("DROP")] = Some(drop.finish(0, &[]));

    // ---- MEMB + MPATH ----------------------------------------------------------------------------
    let mem_in = tree.root();
    let d_in = tree.d;
    assert_eq!(d_in, depth_of(nblk_in), "tree depth at the segment's start");
    let d_out = depth_of(nblk_out);
    // E2E M4c: a depth increase (NEAR: 16 -> 17 at most) lifts the tree first; SEGG is the root
    let lift = d_out > d_in;
    if lift {
        assert!(grow_air && d_out == d_in + 1 && d_in == 16, "depth {d_in} -> {d_out}: only the lift 16 -> 17 is supported");
        tree.lift();
    }
    let mut membg = if grow_air { Some(Tb::new(&seg.tables[si("MEMBG")])) } else { None };
    // MEMBG blocks per grow time (MEMG's lookup multiplicity `gm`)
    let mut gm: HashMap<u64, u64> = HashMap::new();
    let zleaf = leaf_hash(&[0u64; 1024]);
    let mut memb0 = Tb::new(&seg.tables[si("MEMB")]);
    // MEMBH (`wasmBaseSegAirG`): MEMB for old blocks `>= 2^16` (grown in an earlier segment)
    let mut membh = if grow_air { Some(Tb::new(&seg.tables[si("MEMBH")])) } else { None };
    let mut mp = Tb::new(&seg.tables[si("MPATH")]);
    let (mut nro, nb) = (0usize, c1.touched.len());
    let comps0 = sha.comps.len();
    let mut comps_mpath = 0usize;
    // `wasmBaseSegAirMP`: MPATH is the batched multiproof (one row per touched node)
    let multiproof = mp.spec.cols.iter().any(|c| c == "idx");
    let mut mp_leaves: Vec<(u64, bool, [u64; 6])> = vec![];
    for (kb, &b) in c1.touched.iter().enumerate() {
        let base = b << 10;
        if b >= nblk_in {
            // E2E M4c: a block grown in this segment (MEMBG): zero bytes produced at the grow's time,
            // the final bytes hashed, the old leaf is the zero leaf
            let mg = membg.as_mut().expect("a grown block needs the segment AIR airSegG");
            let &(tg, gold, gnew) = c1.grows.iter().find(|g| 64 * g.1 <= b && b < 64 * g.2).expect("grown block without a grow");
            assert!(tg > t_in && tg <= t_out, "block {b} grown outside the segment");
            assert_eq!(tree.lv[0][b as usize], zleaf, "grown block {b}: old leaf is not the zero leaf");
            *gm.entry(tg).or_default() += 1;
            // a byte the segment never accessed keeps MEMBG's own message (time `tg`)
            let bout: Vec<(u64, u64)> = (0..1024)
                .map(|i| {
                    let (v, tp) = c1.mem_end[&(base + i)];
                    if tp == t_in {
                        assert_eq!(v, 0);
                        (0, tg)
                    } else {
                        (v, tp)
                    }
                })
                .collect();
            let mut ho = SHA384_IV;
            for row in 0..9usize {
                mg.push();
                mg.u("act", 1);
                mg.u(&format!("p{row}"), 1);
                mg.u("blk", b);
                mg.u("tg", tg);
                mg.u("gold", gold);
                mg.u("gnew", gnew);
                let bo: Vec<u64> = if row < 8 { (0..128).map(|i| bout[128 * row + i].0).collect() } else { vec![0; 128] };
                if row < 8 {
                    for i in 0..128 {
                        mg.u(&format!("bo{i}"), bo[i]);
                        mg.u(&format!("tq{i}"), bout[128 * row + i].1);
                    }
                    for w in 0..16 {
                        mg.u(&format!("so5_{w}"), bo[8 * w + 5] >> 5);
                        mg.u(&format!("so2_{w}"), bo[8 * w + 2] >> 2);
                    }
                }
                let blk_out = if row < 8 { be_words(&bo) } else { pad_block(8192) };
                let (cid, out) = sha.comp(ho, blk_out);
                mg.u("cidO", cid);
                for (i, l) in limbs24(&ho).into_iter().enumerate() {
                    mg.u(&format!("hiO{i}"), l);
                }
                for (i, l) in limbs24(&out).into_iter().enumerate() {
                    mg.u(&format!("hoO{i}"), l);
                }
                ho = out;
            }
            mp_leaves.push((b, false, d6(&ho)));
            let _ = kb;
            continue;
        }
        let bin: Vec<u64> = (0..1024).map(|i| c1.mem_start[&(base + i)]).collect();
        let bout: Vec<(u64, u64)> = (0..1024).map(|i| c1.mem_end[&(base + i)]).collect();
        let ro = bin.iter().zip(bout.iter()).all(|(a, o)| *a == o.0);
        nro += ro as usize;
        let memb: &mut Tb = if b >= 1 << 16 { membh.as_mut().expect("a block above 64 MiB needs airSegG") } else { &mut memb0 };
        let (mut hi, mut ho) = (SHA384_IV, SHA384_IV);
        for row in 0..9usize {
            memb.push();
            memb.u("act", 1);
            memb.u(&format!("p{row}"), 1);
            memb.u("blk", b);
            memb.u("ro", ro as u64);
            let (bi, bo): (Vec<u64>, Vec<u64>) = if row < 8 {
                ((0..128).map(|i| bin[128 * row + i]).collect(), (0..128).map(|i| bout[128 * row + i].0).collect())
            } else {
                (vec![0; 128], vec![0; 128])
            };
            if row < 8 {
                for i in 0..128 {
                    memb.u(&format!("bi{i}"), bi[i]);
                    memb.u(&format!("bo{i}"), bo[i]);
                    memb.u(&format!("tq{i}"), bout[128 * row + i].1);
                }
                for w in 0..16 {
                    memb.u(&format!("si5_{w}"), bi[8 * w + 5] >> 5);
                    memb.u(&format!("si2_{w}"), bi[8 * w + 2] >> 2);
                    if !ro {
                        memb.u(&format!("so5_{w}"), bo[8 * w + 5] >> 5);
                        memb.u(&format!("so2_{w}"), bo[8 * w + 2] >> 2);
                    }
                }
            }
            let blk_in = if row < 8 { be_words(&bi) } else { pad_block(8192) };
            let (cid, out) = sha.comp(hi, blk_in);
            memb.u("cidI", cid);
            for (i, l) in limbs24(&hi).into_iter().enumerate() {
                memb.u(&format!("hiI{i}"), l);
            }
            for (i, l) in limbs24(&out).into_iter().enumerate() {
                memb.u(&format!("hoI{i}"), l);
            }
            hi = out;
            if !ro {
                let blk_out = if row < 8 { be_words(&bo) } else { pad_block(8192) };
                let (cid, out) = sha.comp(ho, blk_out);
                memb.u("cidO", cid);
                for (i, l) in limbs24(&ho).into_iter().enumerate() {
                    memb.u(&format!("hiO{i}"), l);
                }
                for (i, l) in limbs24(&out).into_iter().enumerate() {
                    memb.u(&format!("hoO{i}"), l);
                }
                ho = out;
            } else if row == 8 {
                for (i, l) in limbs24(&hi).into_iter().enumerate() {
                    memb.u(&format!("hoO{i}"), l);
                }
            }
        }
        let leaf_in = d6(&hi);
        let leaf_out = if ro { leaf_in } else { d6(&ho) };
        assert_eq!(leaf_in, tree.lv[0][b as usize], "block {b}: in-leaf is not the tree's (memory model mismatch)");
        if multiproof {
            mp_leaves.push((b, ro, leaf_out));
            continue;
        }
        // MPATH: old and new path, root chain
        let r_in = tree.root();
        tree.lv[0][b as usize] = leaf_out;
        let (mut co, mut cn) = (leaf_in, leaf_out);
        let mut acc = 0u64;
        let nc_before = sha.comps.len();
        for l in 0..tree.d {
            let idx = (b >> l) as usize;
            let bit = (idx & 1) as u64;
            let sib = tree.lv[l][idx ^ 1];
            acc += bit << l;
            let (lo, ro_) = if bit == 1 { (sib, co) } else { (co, sib) };
            let (cido, oo) = sha.comp(SHA384_IV, node_block(&lo, &ro_));
            let (ln, rn) = if bit == 1 { (sib, cn) } else { (cn, sib) };
            let (cidn, on) = if ro {
                (0, oo)
            } else {
                sha.comp(SHA384_IV, node_block(&ln, &rn))
            };
            mp.push();
            mp.u("act", 1);
            mp.u("bot", (l == 0) as u64);
            mp.u("top", (l + 1 == tree.d) as u64);
            mp.u("bit", bit);
            mp.u("ro", ro as u64);
            mp.u("blk", b);
            mp.u("lvl", l as u64);
            mp.u("acc", acc);
            mp.u("pw", 1 << l);
            mp.u("kb", kb as u64);
            mp.u("cidO", cido);
            mp.u("cidN", cidn);
            for (pre, val) in [("co", &co), ("cn", &cn), ("sb", &sib)] {
                for (i, x) in limbs18(val).into_iter().enumerate() {
                    mp.u(&format!("{pre}{i}"), x);
                }
            }
            for (pre, val) in [("po", &oo), ("pn", &on)] {
                for (i, x) in limbs24(val).into_iter().enumerate() {
                    if i < 18 {
                        mp.u(&format!("{pre}{i}"), x);
                    } else {
                        mp.u(&format!("{}{}", if pre == "po" { "xo" } else { "xn" }, i - 18), x);
                    }
                }
            }
            co = d6(&oo);
            cn = d6(&on);
            tree.lv[l + 1][idx >> 1] = cn;
        }
        comps_mpath += sha.comps.len() - nc_before;
        assert_eq!(co, r_in, "old path does not reach the root");
        // root chain columns, constant per block
        let n = mp.rows.len();
        for r in (n - tree.d)..n {
            for (i, x) in limbs18(&r_in).into_iter().enumerate() {
                let c = mp.col(&format!("ri{i}"));
                mp.rows[r][c] = fe(x);
            }
            for (i, x) in limbs18(&tree.root()).into_iter().enumerate() {
                let c = mp.col(&format!("rt{i}"));
                mp.rows[r][c] = fe(x);
            }
        }
    }
    let mut lift_root: Option<LiftRoot> = None;
    if multiproof {
        let nc_before = sha.comps.len();
        lift_root = multiproof_rows(&mut mp, &mut sha, tree, &mp_leaves, lift);
        comps_mpath += sha.comps.len() - nc_before;
    } else {
        assert!(!grow_air, "airSegG has the multiproof MPATH");
    }
    if let Some(lr) = &lift_root {
        assert_eq!(lr.old_l, mem_in, "lift: the old root is the left child");
    }
    let comps_memb = sha.comps.len() - comps0 - comps_mpath;
    let mem_out = tree.root();
    mats[si("MEMB")] = Some(memb0.finish(0, &[]));
    if let Some(mh) = membh {
        mats[si("MEMBH")] = Some(mh.finish(0, &[]));
    }
    mats[si("MPATH")] = Some(mp.finish(0, &[]));
    if let Some(mg) = membg {
        mats[si("MEMBG")] = Some(mg.finish(0, &[]));
    }
    if grow_air {
        // MEMG: the grow rows' lookup multiplicity, and the size message's final producer time
        let i = si("MEMG");
        let spec = &seg.tables[i];
        let m = mats[i].as_mut().unwrap();
        let w = spec.cols.len();
        let (cts, cok, cgm, cfg, cfs) = (spec.col("ts"), spec.col("ok"), spec.col("gm"), spec.col("f_grow"), spec.col("f_size"));
        let mut tz = t_in;
        let mut used = 0u64;
        for r in m.values.chunks_mut(w) {
            if r[cfg] == F::ZERO && r[cfs] == F::ZERO {
                continue;
            }
            let ts = r[cts].as_canonical_u32() as u64;
            tz = tz.max(ts);
            let g = if r[cok] == F::ONE { gm.get(&ts).copied().unwrap_or(0) } else { 0 };
            used += g;
            r[cgm] = fe(g);
        }
        assert_eq!(used, gm.values().sum::<u64>(), "MEMBG block without its MEMG grow row");
        // SEGG: the size message across the cut, and the lift root
        let mut sg = Tb::new(&seg.tables[si("SEGG")]);
        sg.push();
        sg.u("pin", c0.pages);
        sg.u("pout", c1.pages);
        sg.u("tz", tz);
        if let Some(lr) = &lift_root {
            sg.u("lift", 1);
            sg.u("ndL", lr.nd[0] as u64);
            sg.u("ndR", lr.nd[1] as u64);
            sg.u("cidN", lr.cid);
            for (pre, val) in [("oL", &lr.old_l), ("nL", &lr.new[0]), ("nR", &lr.new[1])] {
                for (i, x) in limbs18(val).into_iter().enumerate() {
                    sg.u(&format!("{pre}{i}"), x);
                }
            }
            for (i, x) in limbs24(&lr.out).into_iter().enumerate() {
                if i < 18 {
                    sg.u(&format!("pn{i}"), x);
                } else {
                    sg.u(&format!("xn{}", i - 18), x);
                }
            }
        }
        mats[si("SEGG")] = Some(sg.finish(0, &[]));
    }

    // ---- SEGB --------------------------------------------------------------------------------------
    let depth_out = c1.depth_of.iter().find(|x| x.0 == c1.cid).map(|x| x.1).unwrap();
    let mut sb = Tb::new(&seg.tables[si("SEGB")]);
    sb.push();
    sb.u("cidf", c1.cid);
    sb.u("m0", *lookups.get(&0).unwrap_or(&0));
    sb.u("gtpf", if c1.gas.2 <= t_in { t_in } else { c1.gas.2 });
    // the multiproof's root row closes RCH with `[1] ++ memOut`
    sb.u("nbt", if multiproof { (nb > 0 || lift) as u64 } else { nb as u64 });
    mats[si("SEGB")] = Some(sb.finish(0, &[]));

    let depth_in = c0.depth_of.iter().find(|x| x.0 == c0.cid).map(|x| x.1).unwrap();
    let b_in = Bnd { pc: c0.pc, t: t_in, s: c0.s, sb: c0.sb, cid: depth_in, sseg: c0.gas.0, segb: c0.gas.1, ctx: ctx_in, mem: mem_in,
        nblk: nblk_in, depth: d_in as u64 };
    let b_out = Bnd { pc: c1.pc, t: t_out, s: c1.s, sb: c1.sb, cid: depth_out, sseg: c1.gas.0, segb: c1.gas.1, ctx: ctx_out, mem: mem_out,
        nblk: nblk_out, depth: d_out as u64 };
    assert_eq!(tree.d, d_out);
    let mut pubs = pubs_of(&b_in, &b_out, c1.halted, prep, tree.d as u64);
    if grow_air {
        pubs[PUB_NBLK] = fe(nblk_in.min(1 << 16));
        pubs.push(fe(nblk_in));
        pubs.push(fe(nblk_out));
        pubs.push(fe(d_in as u64));
        assert_eq!(pubs.len(), NUM_PUB_G);
    }
    assert_eq!(pubs.len(), seg.num_pub);

    // ---- lookup tables -------------------------------------------------------------------------------
    for name in ["RANGE16", "BYTE", "CODE", "FUNC", "HOSTT"] {
        let (_, fm) = full(name);
        mats[si(name)] = Some(fm.clone());
    }
    let mut mats: Vec<RowMajorMatrix<F>> = mats.into_iter().enumerate().map(|(i, m)| m.unwrap_or_else(|| panic!("table {} not built", seg.tables[i].name))).collect();
    recount(seg, &mut mats, &pubs);
    let stats = SegStats {
        blocks: nb,
        blocks_ro: nro,
        stream_in: ein.len(),
        stream_out: eout.len(),
        drops: c1.dead.len(),
        tombs: c1.tombs.len(),
        comps: sha.comps.len(),
        comps_stream,
        comps_memb,
        comps_mpath,
        pages: (c0.pages, c1.pages),
        grown: c1.touched.iter().filter(|&&b| b >= nblk_in).count(),
        high: c1.touched.iter().filter(|&&b| b >= 1 << 16 && b < nblk_in).count(),
        lift,
    };
    SegInst { mats, pubs, comps: sha.comps, b_in, b_out, halted: c1.halted, stats }
}

/// `wasmBaseSegAirMP`'s MPATH: one row per touched node `(lvl, idx)`, `1 ≤ lvl ≤ D`, hashing it
/// once with the old children and once with the new ones (skipped when both children are
/// unchanged).  `leaves`: the touched blocks `(blk, ro, new leaf)`; `tree` is the tree at the
/// segment's start and is advanced to its end.
fn multiproof_rows(mp: &mut Tb, sha: &mut Sha, tree: &mut Tree, leaves: &[(u64, bool, [u64; 6])], lift: bool) -> Option<LiftRoot> {
    if leaves.is_empty() && !lift {
        return None;
    }
    assert!(tree.d <= 30, "the multiproof's level bits need D ≤ 30");
    // touched positions of the current level: new digest and (level 0) the leaf's ro flag
    let mut cur: BTreeMap<usize, ([u64; 6], u64)> = leaves.iter().map(|&(b, ro, d)| (b as usize, (d, ro as u64))).collect();
    for lvl in 1..=tree.d {
        if lift && lvl == tree.d {
            // E2E M4c: SEGG's lift row is the root `(D, 0)`: old children = the in-root and `Z_{D-1}`
            // (never hashed), new children from the touched nodes `(D-1, 0/1)`; one compression
            let z = zero_roots(tree.d - 1)[tree.d - 1];
            let old = [tree.lv[lvl - 1][0], tree.lv[lvl - 1][1]];
            assert_eq!(old[1], z, "lift: the right subtree is not all-zero");
            let nd = [cur.contains_key(&0), cur.contains_key(&1)];
            let new = [0usize, 1].map(|s| cur.get(&s).map(|x| x.0).unwrap_or(old[s]));
            let (cid, out) = sha.comp(SHA384_IV, node_block(&new[0], &new[1]));
            for (&i, &(d, _)) in cur.iter() {
                tree.lv[lvl - 1][i] = d;
            }
            tree.lv[lvl][0] = d6(&out);
            return Some(LiftRoot { nd, old_l: old[0], new, cid, out });
        }
        let mut next: BTreeMap<usize, ([u64; 6], u64)> = BTreeMap::new();
        let parents: std::collections::BTreeSet<usize> = cur.keys().map(|&i| i >> 1).collect();
        for n in parents {
            mp.push();
            mp.u("act", 1);
            mp.u("top", (lvl == tree.d) as u64);
            mp.u("lvl", lvl as u64);
            mp.u("idx", n as u64);
            for i in 0..5 {
                mp.u(&format!("a{i}"), ((lvl - 1) >> i) as u64 & 1);
                mp.u(&format!("b{i}"), ((tree.d - lvl) >> i) as u64 & 1);
            }
            let mut kids = [([0u64; 6], [0u64; 6]); 2];
            for (s, side) in ["L", "R"].iter().enumerate() {
                let ci = 2 * n + s;
                let old = tree.lv[lvl - 1][ci];
                let new = match cur.get(&ci) {
                    Some(&(d, ro)) => {
                        if lvl == 1 {
                            mp.u(&format!("lf{side}"), 1);
                            mp.u(&format!("r{side}"), ro);
                        } else {
                            mp.u(&format!("nd{side}"), 1);
                        }
                        d
                    }
                    None => old,
                };
                for (i, x) in limbs18(&old).into_iter().enumerate() {
                    mp.u(&format!("o{side}{i}"), x);
                }
                for (i, x) in limbs18(&new).into_iter().enumerate() {
                    mp.u(&format!("n{side}{i}"), x);
                }
                kids[s] = (old, new);
            }
            let ro = kids[0].0 == kids[0].1 && kids[1].0 == kids[1].1;
            mp.u("ro", ro as u64);
            let (cido, oo) = sha.comp(SHA384_IV, node_block(&kids[0].0, &kids[1].0));
            assert_eq!(d6(&oo), tree.lv[lvl][n], "node ({lvl}, {n}): old digest is not the tree's");
            let (cidn, on) = if ro { (0, oo) } else { sha.comp(SHA384_IV, node_block(&kids[0].1, &kids[1].1)) };
            mp.u("cidO", cido);
            mp.u("cidN", cidn);
            for (pre, x2, val) in [("po", "xo", &oo), ("pn", "xn", &on)] {
                for (i, x) in limbs24(val).into_iter().enumerate() {
                    if i < 18 {
                        mp.u(&format!("{pre}{i}"), x);
                    } else {
                        mp.u(&format!("{x2}{}", i - 18), x);
                    }
                }
            }
            next.insert(n, (d6(&on), 0));
        }
        // advance the tree one level
        for (&i, &(d, _)) in cur.iter() {
            tree.lv[lvl - 1][i] = d;
        }
        cur = next;
    }
    for (&i, &(d, _)) in cur.iter() {
        tree.lv[tree.d][i] = d;
    }
    None
}

/// SEGG's lift row (`wasmBaseSegAirG`): touched flags and new digests of the root's children, the
/// old left child (the in-root), the compression id and its output.
pub struct LiftRoot {
    pub nd: [bool; 2],
    pub old_l: [u64; 6],
    pub new: [[u64; 6]; 2],
    pub cid: u64,
    pub out: [u64; 8],
}

pub fn pubs_of(b_in: &Bnd, b_out: &Bnd, halted: u64, prep: &Prep, depth: u64) -> Vec<F> {
    let mut p = vec![0u64; NUM_PUB];
    p[PUB_STATUS] = halted;
    p[PUB_MEM] = prep.mem;
    for (base, b) in [(PUB_PC_IN, b_in), (PUB_PC_OUT, b_out)] {
        p[base] = b.pc;
        p[base + 1] = b.t;
        p[base + 2] = b.s;
        p[base + 3] = b.sb;
        p[base + 4] = b.cid;
        p[base + 5] = b.sseg;
        for (i, l) in limbs(b.segb).into_iter().enumerate() {
            p[base + 6 + i] = l;
        }
    }
    for (base, d) in [(PUB_CTX_IN, &b_in.ctx), (PUB_CTX_OUT, &b_out.ctx), (PUB_MEM_IN, &b_in.mem), (PUB_MEM_OUT, &b_out.mem)] {
        for (i, l) in limbs18(d).into_iter().enumerate() {
            p[base + i] = l;
        }
    }
    p[PUB_DEPTH] = depth;
    p[PUB_NBLK] = prep.mem >> 10;
    p.into_iter().map(fe).collect()
}

fn sel(r: usize, h: usize) -> [F; 3] {
    [fe((r == 0) as u64), fe((r == h - 1) as u64), fe((r != h - 1) as u64)]
}

/// Recount the lookup multiplicities (RANGE16, BYTE, CODE, FUNC, HOSTT) from every row's sends.
pub fn recount(spec: &AirSpec, mats: &mut [RowMajorMatrix<F>], pubs: &[F]) {
    let lookup_buses = [1u16, 3, 4, 6, 9];
    let mut cnt: HashMap<(u16, Vec<u32>), u64> = HashMap::new();
    let skip = ["RANGE16", "BYTE", "CODE", "FUNC", "HOSTT"];
    for (ti, t) in spec.tables.iter().enumerate() {
        if skip.contains(&t.name.as_str()) {
            continue;
        }
        let m = &mats[ti];
        let w = t.cols.len();
        let h = m.values.len() / w;
        let inters: Vec<_> = t.inters.iter().filter(|i| i.send && lookup_buses.contains(&i.bus)).collect();
        for r in 0..h {
            let cur = &m.values[r * w..(r + 1) * w];
            let nxt = &m.values[((r + 1) % h) * w..((r + 1) % h + 1) * w];
            let sl = sel(r, h);
            for it in inters.iter() {
                let c = it.count.eval_f(cur, nxt, pubs, sl).as_canonical_u32();
                if c == 0 {
                    continue;
                }
                let msg: Vec<u32> = it.msg.iter().map(|e| e.eval_f(cur, nxt, pubs, sl).as_canonical_u32()).collect();
                *cnt.entry((it.bus, msg)).or_default() += c as u64;
            }
        }
    }
    for (ti, t) in spec.tables.iter().enumerate() {
        if !skip.contains(&t.name.as_str()) {
            continue;
        }
        let w = t.cols.len();
        let h = mats[ti].values.len() / w;
        let col = |n: &str| t.col(n);
        let mut seen: HashMap<(u16, Vec<u32>), ()> = HashMap::new();
        for r in 0..h {
            let row: Vec<u32> = mats[ti].values[r * w..(r + 1) * w].iter().map(|x| x.as_canonical_u32()).collect();
            let mut set = |c: usize, key: (u16, Vec<u32>)| {
                let v = if seen.insert(key.clone(), ()).is_none() { *cnt.get(&key).unwrap_or(&0) } else { 0 };
                mats[ti].values[r * w + c] = fe(v);
            };
            match t.name.as_str() {
                "RANGE16" => set(col("m"), (3, vec![row[col("v")]])),
                "BYTE" => {
                    let x: u32 = (0..8).map(|i| row[col(&format!("x{i}"))] << i).sum();
                    let y: u32 = (0..8).map(|i| row[col(&format!("y{i}"))] << i).sum();
                    for (k, res) in [(0u32, 0u32), (1, x & y), (2, x | y), (3, x ^ y)] {
                        set(col(&format!("m{k}")), (4, vec![k, x, y, res]));
                    }
                }
                "CODE" => set(col("mult"), (1, row[..8].to_vec())),
                "FUNC" => set(col("mult"), (6, row[..8].to_vec())),
                "HOSTT" => set(col("mult"), (9, row[..8].to_vec())),
                _ => unreachable!(),
            }
        }
    }
}

/// The chip's interface sends for a list of compressions (what the native SHA-512 AIR emits).
pub fn chip_if(comps: &[Comp]) -> Vec<Vec<u32>> {
    let mut out = vec![];
    for (s, c) in comps.iter().enumerate() {
        let o = sha2_compress(c);
        let ws: Vec<u64> = c.h.iter().chain(c.block.iter()).chain(o.iter()).copied().collect();
        for m in 0..16 {
            let mut msg = vec![(s * 128) as u32, m as u32];
            for w in [ws[2 * m], ws[2 * m + 1]] {
                msg.extend(wl(w).map(|x| x as u32));
            }
            out.push(msg);
        }
    }
    out
}

/// Constraint check on every row and bus balance over every table plus the chip's sends.
pub fn precheck(spec: &AirSpec, mats: &[RowMajorMatrix<F>], pubs: &[F], comps: &[Comp]) -> Result<(), String> {
    let mut bal: HashMap<(u16, Vec<u32>), i128> = HashMap::new();
    // the first (table, row) that touches each message (diagnostics only)
    let mut who: HashMap<(u16, Vec<u32>), (String, usize)> = HashMap::new();
    for (ti, t) in spec.tables.iter().enumerate() {
        let m = &mats[ti];
        let w = t.cols.len();
        let h = m.values.len() / w;
        for r in 0..h {
            let cur = &m.values[r * w..(r + 1) * w];
            let nxt = &m.values[((r + 1) % h) * w..((r + 1) % h + 1) * w];
            let sl = sel(r, h);
            for (ci, c) in t.constraints.iter().enumerate() {
                let v = c.eval_f(cur, nxt, pubs, sl);
                if v != F::ZERO {
                    return Err(format!("{} row {r} constraint {ci} = {}", t.name, v.as_canonical_u32()));
                }
            }
            for it in &t.inters {
                let c = it.count.eval_f(cur, nxt, pubs, sl).as_canonical_u32();
                if c == 0 {
                    continue;
                }
                let msg: Vec<u32> = it.msg.iter().map(|e| e.eval_f(cur, nxt, pubs, sl).as_canonical_u32()).collect();
                let c = if c > (P as u32) / 2 { -((P - c as u64) as i128) } else { c as i128 };
                who.entry((it.bus, msg.clone())).or_insert((t.name.clone(), r));
                *bal.entry((it.bus, msg)).or_insert(0) += if it.send { c } else { -c };
            }
        }
    }
    for msg in chip_if(comps) {
        *bal.entry((103, msg)).or_insert(0) += 1;
    }
    let mut bad: Vec<_> = bal.iter().filter(|(_, v)| **v != 0).collect();
    bad.sort_by_key(|((b, m), _)| (*b, m.clone()));
    if bad.is_empty() {
        Ok(())
    } else {
        let mut by: BTreeMap<u16, usize> = BTreeMap::new();
        for ((b, _), _) in bad.iter() {
            *by.entry(*b).or_default() += 1;
        }
        let first: Vec<_> = bad[..bad.len().min(3)].iter().map(|(k, v)| (k.clone(), **v, who.get(*k).cloned())).collect();
        Err(format!("{} unbalanced messages by bus {:?}; first {:?}", bad.len(), by, first))
    }
}
