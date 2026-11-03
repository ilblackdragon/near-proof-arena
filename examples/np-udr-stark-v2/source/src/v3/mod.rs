//! Honest per-table trace generators for `nearAirV3` (part 2 of the v2 prover).
//!
//! Each `*_aligned` function is the Rust twin of a Lean aligned generator:
//! `ZkFormal.NearV3.Render.{bnd,akey,head,val}TraceAligned` (`Render/Padded.lean`)
//! and `{uniq,walk}TraceAligned` (`Render/PaddedTrie.lean`).  The input is the
//! table's entry list (the Lean structure of the same name, deserialized from
//! JSON with the Lean field names); the output is the trace at the aligned
//! height `padLog22 (logOf n)` with every cell reduced mod `P` (`Fp.ofNat`).
//! `conformance/run-v2.sh` compares the dumps with `np-lean-render-v3` byte for
//! byte.
//!
//! The Lean cells are functions of unbounded naturals; here the scalar fields
//! are `u64`.  The one place where that matters is `uniq`, whose cells compare
//! 256-bit keys: [`uniq_aligned`] requires the shape of `UOk.mem` (32 bytes,
//! each `< 256`) and returns an error otherwise.

use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use serde::Deserialize;

use crate::field::{F, P};

pub mod acct;
pub mod chacha;
pub mod collect;
pub mod d0;
pub mod d1;
pub mod entries;
pub mod forest;
pub mod hint;
pub mod mrksort;
pub mod native;
pub mod node;
pub mod prep;
pub mod prove;
pub mod public;
pub mod qv;
pub mod rcpt;
pub mod rcptfam;
pub mod sample;
pub mod sched;
pub mod schedqv;
pub mod sha;
pub mod size;
pub mod statement;
pub mod srcp;
pub mod trie;
pub mod ups;
pub mod upsnat;
pub mod walks;

/// A generated table: `2^log` rows of `width` canonical cells, row-major.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tab {
    pub log: usize,
    pub width: usize,
    pub cells: Vec<u32>,
}

impl Tab {
    fn zero(log: usize, width: usize) -> Tab {
        Tab {
            log,
            width,
            cells: vec![0; width << log],
        }
    }
    pub fn height(&self) -> usize {
        1 << self.log
    }
    pub fn set(&mut self, r: usize, c: usize, x: u64) {
        self.cells[r * self.width + c] = (x % P as u64) as u32;
    }
    /// The `np-render-v3-table` dump: `log, width`, then the cells (u32 LE).
    pub fn dump(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(8 + 4 * self.cells.len());
        b.extend_from_slice(&(self.log as u32).to_le_bytes());
        b.extend_from_slice(&(self.width as u32).to_le_bytes());
        for &x in &self.cells {
            b.extend_from_slice(&x.to_le_bytes());
        }
        b
    }
    pub fn to_matrix(&self) -> p3_matrix::dense::RowMajorMatrix<F> {
        p3_matrix::dense::RowMajorMatrix::new(
            self.cells.iter().map(|&x| F::from_u32(x)).collect(),
            self.width,
        )
    }
}

/// `clog2`, `logOf = max 1 ∘ clog2` (`Near/Render/Common.lean`).
pub fn log_of(n: usize) -> usize {
    crate::near::info::log_of(n)
}

/// `padLog22 l = 22 − 3·((22 − l) / 3)` (`Size/PadHeader.lean`, truncating `−`).
pub fn pad_log22(l: usize) -> usize {
    22 - 3 * (22usize.saturating_sub(l) / 3)
}

fn get(xs: &[u64], i: usize) -> u64 {
    xs.get(i).copied().unwrap_or(0)
}

fn b(x: bool) -> u64 {
    x as u64
}

// ---------------------------------------------------------------- bnd (19)

pub const BND_WIDTH: usize = 6;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct BndE {
    pub x: u64,
    pub lo: u64,
    pub hi: u64,
    pub hn: u64,
    #[serde(rename = "U")]
    pub u: u64,
}

/// `bndTraceAligned`: row `q < |es|` is `[1, x, lo, hi, hn, U]`.
pub fn bnd_aligned(es: &[BndE]) -> Tab {
    let mut t = Tab::zero(pad_log22(log_of(es.len())), BND_WIDTH);
    for (q, e) in es.iter().enumerate().take(t.height()) {
        for (c, x) in [1, e.x, e.lo, e.hi, e.hn, e.u].into_iter().enumerate() {
            t.set(q, c, x);
        }
    }
    t
}

// --------------------------------------------------------------- akey (18)

pub const AKEY_WIDTH: usize = 7;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct AkeyE {
    pub vid: u64,
    #[serde(rename = "U")]
    pub u: u64,
    pub bytes: Vec<u64>,
}

/// `akeyTraceAligned`: record `s` on rows `9s … 9s+8`, lane `p`:
/// `[1, [p=0], [p=8], vid, p, bytes[p], U]`.
pub fn akey_aligned(es: &[AkeyE]) -> Tab {
    let mut t = Tab::zero(pad_log22(log_of(9 * es.len())), AKEY_WIDTH);
    for q in 0..(9 * es.len()).min(t.height()) {
        let (e, p) = (&es[q / 9], q % 9);
        let row = [
            1,
            b(p == 0),
            b(p == 8),
            e.vid,
            p as u64,
            get(&e.bytes, p),
            e.u,
        ];
        for (c, x) in row.into_iter().enumerate() {
            t.set(q, c, x);
        }
    }
    t
}

// ---------------------------------------------------------------- head (3)

pub const HEAD_WIDTH: usize = 73;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct HeadE {
    pub tau: u64,
    pub rid: u64,
    pub rlen: u64,
    pub rres: u64,
    #[serde(rename = "mE")]
    pub m_e: u64,
    pub pre: Vec<u64>,
    pub post: Vec<u64>,
}

/// `headTraceAligned`: head `t` on rows `32t + i`: `[1, [i=0], [i=31], τ, rid, rlen,
/// rres, i, mE]`, then `reg m = pre[m+i]` and `preg m = post[m+i]` (`m < 32`).
pub fn head_aligned(hs: &[HeadE]) -> Tab {
    let mut t = Tab::zero(pad_log22(log_of(32 * hs.len())), HEAD_WIDTH);
    for q in 0..(32 * hs.len()).min(t.height()) {
        let (h, i) = (&hs[q / 32], q % 32);
        let head = [
            1,
            b(i == 0),
            b(i == 31),
            h.tau,
            h.rid,
            h.rlen,
            h.rres,
            i as u64,
            h.m_e,
        ];
        for (c, x) in head.into_iter().enumerate() {
            t.set(q, c, x);
        }
        for m in 0..32 {
            t.set(q, 9 + m, get(&h.pre, m + i));
            t.set(q, 41 + m, get(&h.post, m + i));
        }
    }
    t
}

// ----------------------------------------------------------------- val (4)

pub const VAL_WIDTH: usize = 15;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct ValE {
    pub vid: u64,
    pub len: u64,
    pub vz: bool,
    pub dup: bool,
    pub hd: bool,
    #[serde(rename = "repE")]
    pub rep_e: u64,
    pub bytes: Vec<u64>,
}

impl ValE {
    /// `nOf`: one row for an empty value, else `len`.
    fn n_of(&self) -> u64 {
        if self.vz { 1 } else { self.len }
    }
}

/// `valTraceAligned`: the record rows `(t, p)`, `p < nOf es[t]`, then the `SUM`
/// row (`sumr = 1`), then zero padding; column 11 (`sz`) is `szAt q` on every row.
pub fn val_aligned(es: &[ValE]) -> Tab {
    let r: u64 = es.iter().map(ValE::n_of).sum();
    let r = usize::try_from(r).expect("valV3: row count");
    let mut t = Tab::zero(pad_log22(log_of(r + 1)), VAL_WIDTH);
    let h = t.height();
    let mut q = 0usize;
    let mut sz = 0u64;
    'recs: for e in es {
        let n = e.n_of();
        let gw = b(!(e.vz || e.dup));
        for p in 0..n {
            if q >= h {
                break 'recs;
            }
            let row = [
                1,
                b(p == 0),
                b(p + 1 == n),
                e.vid,
                e.len,
                p,
                get(&e.bytes, p as usize),
                b(e.vz),
                b(e.dup),
                b(e.hd),
                e.rep_e,
                sz,
                0,
                b(!e.vz),
                b(p == 0 && e.dup),
            ];
            for (c, x) in row.into_iter().enumerate() {
                t.set(q, c, x);
            }
            sz += gw;
            q += 1;
        }
    }
    // `szAt q` for `q ≥ R` is the full sum; the `SUM` row is row `R`.
    for q in r.min(h)..h {
        t.set(q, 11, sz);
    }
    if r < h {
        t.set(r, 12, 1);
    }
    t
}

// ------------------------------------------------- A7 accounting (val/node)
//
// `nearAirV3` tables 2/4/7/21 are the A7 extensions `nodeA7`, `valA7`,
// `upsA7`, `sizeA7` (`ZkFormal/NearV3/Tables/UnfoldA7.lean`): the base table
// with columns appended at its old width (`Trace.withCols`,
// `Render/UnfoldA7Ext.lean`), the base cells unchanged.  The honest renders are
// `nodeA7Trace vs t (selN vs S)`, `valA7Trace es t (selV es S)`,
// `upsA7Trace insts t`, `sizeA7Trace pub v t (yA7 y0 y1 y2)`
// (`Render/UnfoldA7Aligned.lean`, instantiated in `Assembly/TrieSide.lean`).
//
// Entry JSON (backwards readable): node/val entries are the old objects with an
// optional `"rpl": bool` per record (default `false`) — the replaced-record
// predicate `S` on record indices (`S n = es[n].rpl`); the size entry has an
// optional `"yN": [y0, y1, y2]` (default zeros, entries past 3 ignored, as
// `yA7`).  `v3check` only checks local constraints, so any `rpl` choice and any
// `yN` with `y0 + y1 + y2 ≤ B0` gives a locally legal trace.

/// `valA7` width: `valV3` (15) + `rplv` (15) + `rb` (16).
pub const VAL_A7_WIDTH: usize = 17;

/// `a + b` in `F` (canonical representatives).
pub(crate) fn fp_add(a: u64, b: u64) -> u64 {
    (a % P as u64 + b % P as u64) % P as u64
}

/// `a − b` in `F`.
pub(crate) fn fp_sub(a: u64, b: u64) -> u64 {
    (a % P as u64 + P as u64 - b % P as u64) % P as u64
}

/// `a · b` in `F`.
pub(crate) fn fp_mul(a: u64, b: u64) -> u64 {
    (a % P as u64) * (b % P as u64) % P as u64
}

/// `Trace.withCols` with zero new columns: `t` widened to `w` columns.
pub(crate) fn widen(t: &Tab, w: usize) -> Tab {
    let mut o = Tab::zero(t.log, w);
    for r in 0..t.height() {
        o.cells[r * w..r * w + t.width].copy_from_slice(&t.cells[r * t.width..(r + 1) * t.width]);
    }
    o
}

/// `nodeCols` / `valCols` (`Render/UnfoldA7Ext.lean`) written into columns
/// `bw` (`rpl`) and `bw + 1` (running sum) of the widened table `t`:
/// `rpl r = [sel r ∧ cell r first = 1]`, the sum is `prefixF inc` with
/// `inc r = 2·cell r act − cell r first · rpl r · cell r len` (in `F`).
pub(crate) fn a7_record_cols(
    t: &mut Tab,
    bw: usize,
    (act, first, len): (usize, usize, usize),
    sel: impl Fn(usize) -> bool,
) {
    let w = t.width;
    let mut acc = 0u64;
    for r in 0..t.height() {
        let c = |x: usize| t.cells[r * w + x] as u64;
        let rpl = (sel(r) && c(first) == 1) as u64;
        let inc = fp_sub(fp_mul(2, c(act)), fp_mul(fp_mul(c(first), rpl), c(len)));
        t.set(r, bw, rpl);
        t.set(r, bw + 1, acc);
        acc = fp_add(acc, inc);
    }
}

/// Parse a JSON list of entry objects and their optional `"rpl"` flags
/// (absent → `false`).
pub(crate) fn parse_rpl<T: serde::de::DeserializeOwned>(
    json: &str,
) -> Result<(Vec<T>, Vec<bool>), String> {
    let v: serde_json::Value = serde_json::from_str(json).map_err(|e| e.to_string())?;
    let arr = v.as_array().ok_or("expected a JSON list of entries")?;
    let mut es = Vec::with_capacity(arr.len());
    let mut sel = Vec::with_capacity(arr.len());
    for (i, x) in arr.iter().enumerate() {
        sel.push(match x.get("rpl") {
            None | Some(serde_json::Value::Null) => false,
            Some(serde_json::Value::Bool(b)) => *b,
            Some(o) => return Err(format!("entry {i}: \"rpl\" must be a boolean, got {o}")),
        });
        es.push(serde_json::from_value(x.clone()).map_err(|e| format!("entry {i}: {e}"))?);
    }
    Ok((es, sel))
}

/// `valA7Trace es t (selV es S)` with `S t = rpl[t]` (absent → `false`):
/// [`val_aligned`] plus `rplv` / `rb` (`valCols`; `act = gb` (13), first-row
/// flag `vf` (1), `len` (4)).  `selV es S q = q < R ∧ S (record of row q)`.
pub fn val_a7(es: &[ValE], rpl: &[bool]) -> Tab {
    let base = val_aligned(es);
    let mut row_rec = Vec::new();
    for (i, e) in es.iter().enumerate() {
        row_rec.extend(std::iter::repeat(i).take(e.n_of() as usize));
    }
    let mut t = widen(&base, VAL_A7_WIDTH);
    a7_record_cols(&mut t, VAL_WIDTH, (13, 1, 4), |q| {
        row_rec
            .get(q)
            .is_some_and(|&i| rpl.get(i).copied().unwrap_or(false))
    });
    t
}

/// Test support for the A7 tables: the exported constraints that read a new
/// column (index `≥ bw`, the base width: the appended constraints and the
/// multiplicity bits of the appended interactions) checked on a rendered
/// trace, so honest A7 columns and tampered ones can be told apart on any base
/// trace.  Needs the `np-lean-export-v3` JSON at `$NEARAIRV3_JSON`; the tests
/// that use it skip (with a note) when it is unset.
#[cfg(test)]
pub(crate) mod a7_test {
    use super::Tab;
    use crate::air::Expr;

    pub fn air() -> Option<crate::air::Air> {
        let Ok(p) = std::env::var("NEARAIRV3_JSON") else {
            eprintln!("NEARAIRV3_JSON unset: skipping the A7 constraint test");
            return None;
        };
        let txt = std::fs::read_to_string(&p).expect("NEARAIRV3_JSON");
        Some(crate::air::Air::from_json(&txt).expect("nearAirV3 json"))
    }

    fn reads_from(e: &Expr, bw: usize) -> bool {
        match e {
            Expr::Col(c, _) => *c >= bw,
            Expr::Add(a, b) | Expr::Mul(a, b) => reads_from(a, bw) || reads_from(b, bw),
            Expr::Neg(a) => reads_from(a, bw),
            _ => false,
        }
    }

    /// `(constraint, row)` pairs failing among the constraints of table `idx`
    /// that read a column `≥ bw`.
    pub fn failing_new(
        air: &crate::air::Air,
        idx: usize,
        bw: usize,
        tab: &Tab,
    ) -> Vec<(usize, usize)> {
        let mut t = air.tables[idx].clone();
        assert_eq!(t.width, tab.width, "table {idx} width");
        t.constraints.retain(|e| reads_from(e, bw));
        assert!(!t.constraints.is_empty());
        let pubs = vec![<crate::field::F as p3_field::PrimeCharacteristicRing>::ZERO; air.num_pub];
        crate::check::failing_constraints(&t, &tab.to_matrix(), &pubs, 20)
    }

    /// The honest `tab` satisfies the appended constraints; adding `1` to any
    /// one of the `cells` `(row, col)` violates one of them.
    pub fn honest_and_tampered(idx: usize, bw: usize, tab: &Tab, cells: &[(usize, usize)]) {
        let Some(air) = air() else { return };
        assert_eq!(
            failing_new(&air, idx, bw, tab),
            vec![],
            "honest table {idx}"
        );
        for &(r, c) in cells {
            let mut t = tab.clone();
            let x = t.cells[r * t.width + c] as u64;
            t.set(r, c, x + 1);
            assert!(
                !failing_new(&air, idx, bw, &t).is_empty(),
                "table {idx}: tampered cell ({r}, {c}) passes"
            );
        }
    }
}

// ---------------------------------------------------------------- uniq (6)

pub const UNIQ_WIDTH: usize = 53;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct UEnt {
    pub eid: u64,
    pub tau: u64,
    pub bytes: Vec<u64>,
}

/// A 256-bit little-endian number (`le256` of 32 bytes).
type U256 = [u8; 32];

fn le256(bs: &[u64]) -> Result<U256, String> {
    if bs.len() != 32 || bs.iter().any(|&x| x >= 256) {
        return Err("uniqV3 entry: bytes must be 32 values < 256 (UOk.mem)".into());
    }
    Ok(std::array::from_fn(|i| bs[i] as u8))
}

/// `x − y − k` over naturals (`0` if negative).
fn sub256(x: &U256, y: &U256, k: u8) -> U256 {
    let mut out = [0u8; 32];
    let mut borrow = k as i32;
    for i in 0..32 {
        let d = x[i] as i32 - y[i] as i32 - borrow;
        out[i] = d.rem_euclid(256) as u8;
        borrow = (d < 0) as i32;
    }
    if borrow != 0 { [0; 32] } else { out }
}

/// `SortGen.carryFrom x y c i` for `i ≤ 32`: the carries of `x + y + c` byte by byte.
fn carries(x: &U256, y: &U256, c: u8) -> [u8; 33] {
    let mut out = [0u8; 33];
    out[0] = c;
    for i in 0..32 {
        out[i + 1] = ((x[i] as u32 + y[i] as u32 + out[i] as u32) / 256) as u8;
    }
    out
}

/// `uniqTraceAligned`: entry `t` on rows `32t + i` (columns 0–20, see
/// `UniqGen.actCell`); the delay line `d j` (column `21 + j`, `j < 32`) is `bb` of
/// row `(q + 2H − 1 − j) mod H` on every row, padding included.
pub fn uniq_aligned(l: &[UEnt]) -> Result<Tab, String> {
    let keys: Vec<U256> = l
        .iter()
        .map(|e| le256(&e.bytes))
        .collect::<Result<_, _>>()?;
    let mut t = Tab::zero(pad_log22(log_of(32 * l.len())), UNIQ_WIDTH);
    let h = t.height();
    let act = (32 * l.len()).min(h);
    let bb = |q: usize| {
        if q < 32 * l.len() {
            keys[q / 32][q % 32] as u64
        } else {
            0
        }
    };
    for (s, e) in l.iter().enumerate() {
        if 32 * s >= h {
            break;
        }
        let same = s != 0 && e.tau == l[s - 1].tau;
        let st = b(s != 0 && !same);
        let eq = same && keys[s] == keys[s - 1];
        let peid = if s == 0 { 0 } else { l[s - 1].eid };
        let k = 1 - eq as u8;
        let (diff, carry) = if same {
            let d = sub256(&keys[s], &keys[s - 1], k);
            let c = carries(&keys[s - 1], &d, k);
            (d, c)
        } else {
            let mut c = [0u8; 33];
            c[0] = 1;
            ([0u8; 32], c)
        };
        for i in 0..32 {
            let q = 32 * s + i;
            if q >= act {
                break;
            }
            let head = [
                1,
                b(i == 0),
                b(i == 31),
                b(s == 0),
                e.eid,
                peid,
                e.tau,
                st,
                eq as u64,
                i as u64,
                keys[s][i] as u64,
                carry[i] as u64,
                carry[i + 1] as u64,
            ];
            for (c, x) in head.into_iter().enumerate() {
                t.set(q, c, x);
            }
            for j in 0..8 {
                t.set(q, 13 + j, ((diff[i] >> j) & 1) as u64);
            }
        }
    }
    for q in 0..h {
        for j in 0..32 {
            // `(q + 2H − 1 − j) % H` with Lean's truncating subtraction.
            let src = (q + 2 * h).saturating_sub(1).saturating_sub(j) % h;
            t.set(q, 21 + j, bb(src));
        }
    }
    Ok(t)
}

// ---------------------------------------------------------------- walk (5)

pub const WALK_WIDTH: usize = 56;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct WStep3 {
    pub mode: u64,
    pub sym: u64,
    pub e: Vec<u64>,
    pub u: u64,
    pub bm: u64,
    pub hv: u64,
    pub ub: u64,
}

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct WalkR {
    pub w: u64,
    pub tau: u64,
    pub steps: Vec<WStep3>,
}

/// `FK_VAL`, `FK_ABS` (`Near/Ids.lean`).
pub const FK_VAL: u64 = 0;
pub const FK_ABS: u64 = 1;

impl WalkR {
    fn last(&self) -> WStep3 {
        self.steps.last().cloned().unwrap_or_default()
    }
    /// `WalkR.fk`, `WalkR.k`.
    fn fk(&self) -> u64 {
        if self.last().mode == 0 {
            FK_VAL
        } else {
            FK_ABS
        }
    }
    fn k(&self) -> u64 {
        let l = self.last();
        if l.mode == 0 { get(&l.e, 3) } else { 0 }
    }
}

/// `invOf`: `(sym − nib)⁻¹` in `Fp` (`0 ↦ 0`).
fn inv_of(s: &WStep3) -> u64 {
    let d = F::from_u64(s.sym) - F::from_u64(get(&s.e, 2));
    d.try_inverse().unwrap_or(F::ZERO).as_canonical_u32() as u64
}

/// `walkTraceAligned`: one row per step `(wv, j)` in table order (`WalkGen.rowCell`).
pub fn walk_aligned(ws: &[WalkR]) -> Tab {
    let rows: usize = ws.iter().map(|w| w.steps.len()).sum();
    let mut t = Tab::zero(pad_log22(log_of(rows)), WALK_WIDTH);
    let h = t.height();
    let mut q = 0;
    'walks: for wv in ws {
        let n = wv.steps.len();
        let (fk, k) = (wv.fk(), wv.k());
        for (j, s) in wv.steps.iter().enumerate() {
            if q >= h {
                break 'walks;
            }
            let last = j + 1 == n;
            let mut row = [0u64; WALK_WIDTH];
            row[..24].copy_from_slice(&[
                1,
                b(j == 0),
                b(last),
                b(j != 0),
                wv.w,
                wv.tau,
                j.saturating_sub(1) as u64,
                s.sym,
                get(&s.e, 0),
                get(&s.e, 1),
                get(&s.e, 2),
                get(&s.e, 3),
                get(&s.e, 4),
                get(&s.e, 5),
                s.u,
                b(s.mode == 0),
                b(s.mode == 1),
                b(s.mode == 2),
                b(s.mode == 3),
                if s.mode == 1 { inv_of(s) } else { 0 },
                if s.mode == 2 { s.hv } else { 0 },
                s.ub,
                if last { fk } else { 0 },
                if last { k } else { 0 },
            ]);
            for i in 0..16 {
                row[24 + i] = if s.mode == 2 { (s.bm >> i) & 1 } else { 0 };
                row[40 + i] = b(s.mode == 2 && !last && s.sym == i as u64);
            }
            for (c, x) in row.into_iter().enumerate() {
                t.set(q, c, x);
            }
            q += 1;
        }
    }
    t
}

/// Table names accepted by [`render`] with their `nearAirV3` table index.
pub const TABLES: &[(&str, usize)] = &[
    ("head", 3),
    ("val", 4),
    ("walk", 5),
    ("uniq", 6),
    ("ups", 7),
    ("acct", 17),
    ("akey", 18),
    ("bnd", 19),
    ("size", 21),
    ("rcpt", 16),
    ("node", 2),
    ("srcp", 20),
    ("qv", 22),
    ("chacha", 8),
    ("rng", 9),
    ("shuf", 10),
    ("codec", 11),
    ("scandist", 12),
    ("proc", 13),
    ("mem", 14),
    ("cmp", 15),
    ("sha_t", 0),
    ("sha_r", 1),
    ("mrk", 23),
    ("sort", 24),
];

/// Parse `json` as the entry list of `table` and render its aligned trace.
pub fn render(table: &str, json: &str) -> Result<Tab, String> {
    fn p<T: for<'a> Deserialize<'a>>(s: &str) -> Result<Vec<T>, String> {
        serde_json::from_str(s).map_err(|e| e.to_string())
    }
    Ok(match table {
        "bnd" => bnd_aligned(&p(json)?),
        "akey" => akey_aligned(&p(json)?),
        "head" => head_aligned(&p(json)?),
        "val" => {
            let (es, rpl) = parse_rpl::<ValE>(json)?;
            val_a7(&es, &rpl)
        }
        "uniq" => uniq_aligned(&p(json)?)?,
        "walk" => walk_aligned(&p(json)?),
        "node" => node::render(json)?,
        "chacha" => chacha::render(json)?,
        "rng" => chacha::render_rng(json)?,
        "shuf" => chacha::render_shuf(json)?,
        "ups" | "rcpt" | "srcp" | "qv" | "sched" | "acct" | "size" => match table {
            "ups" => ups::render(json),
            "rcpt" => rcpt::render(json),
            "srcp" => srcp::render(json),
            "qv" => qv::render(json),
            "sched" => sched::render(json),
            "acct" => acct::render(json),
            _ => size::render(json),
        }?,
        "codec" => sched::codec(json)?,
        "scandist" => sched::scandist(json)?,
        "proc" => sched::proc(json)?,
        "mem" => sched::mem(json)?,
        "cmp" => sched::cmp(json)?,
        "sha_t" | "sha_r" => sha::render(json)?,
        "mrk" => mrksort::render_mrk(json)?,
        "sort" => mrksort::render_sort(json)?,
        t => return Err(format!("unknown table {t}")),
    })
}

#[cfg(test)]
mod tests {
    use super::sample::Rng;
    use super::*;

    #[test]
    fn pad_log22_matches_lean() {
        // `22 − 3·((22 − l) / 3)`: rounds up to the residue 1 mod 3, capped at 22
        let want = [
            1, 1, 4, 4, 4, 7, 7, 7, 10, 10, 10, 13, 13, 13, 16, 16, 16, 19, 19, 19, 22, 22, 22,
        ];
        for (l, w) in want.iter().enumerate() {
            assert_eq!(pad_log22(l), *w, "l = {l}");
        }
        assert_eq!(pad_log22(30), 22);
    }

    #[test]
    fn u256_against_u128() {
        let mut r = Rng::new(5);
        let as_u128 = |x: &U256| x.iter().rev().fold(0u128, |a, &b| a * 256 + b as u128);
        for _ in 0..2000 {
            let mut x = [0u8; 32];
            let mut y = [0u8; 32];
            for i in 0..15 {
                x[i] = r.below(256) as u8;
                y[i] = r.below(256) as u8;
            }
            let k = r.below(2) as u8;
            let (xv, yv) = (as_u128(&x), as_u128(&y));
            let d = sub256(&x, &y, k);
            assert_eq!(as_u128(&d), xv.saturating_sub(yv + k as u128));
            let c = carries(&x, &y, k);
            for (i, &ci) in c.iter().enumerate().take(16) {
                // carry into byte i = ((x mod 256^i) + (y mod 256^i) + k) / 256^i
                let m = 1u128 << (8 * i);
                assert_eq!(ci as u128, ((xv % m) + (yv % m) + k as u128) / m, "i = {i}");
            }
        }
    }

    #[test]
    fn val_sum_row_and_sz() {
        let mut r = Rng::new(3);
        let es = sample::val(&mut r, 9);
        let t = val_aligned(&es);
        let rows: usize = es.iter().map(|e| e.n_of() as usize).sum();
        let total: u64 = es.iter().filter(|e| !e.vz && !e.dup).map(|e| e.len).sum();
        assert_eq!(t.cells[rows * VAL_WIDTH + 12], 1);
        assert_eq!(t.cells[rows * VAL_WIDTH], 0);
        assert_eq!(t.cells[(t.height() - 1) * VAL_WIDTH + 11] as u64, total);
    }

    #[test]
    fn val_a7_total() {
        // `rb` on the `SUM` row is `valA7Total es S = Σ_t (2 − [S t]) · len_t`
        let mut r = Rng::new(4);
        let es = sample::val(&mut r, 11);
        let rpl: Vec<bool> = (0..es.len()).map(|_| r.coin()).collect();
        let t = val_a7(&es, &rpl);
        assert_eq!(t.width, VAL_A7_WIDTH);
        let rows: usize = es.iter().map(|e| e.n_of() as usize).sum();
        let want: u64 = es
            .iter()
            .zip(&rpl)
            .map(|(e, &s)| if s { e.len } else { 2 * e.len })
            .sum();
        assert_eq!(t.cells[rows * VAL_A7_WIDTH + 16] as u64, want);
        assert_eq!(t.cells[16], 0);
        // absent `rpl` reads as false
        let j = serde_json::to_string(&es).unwrap();
        let t0 = render("val", &j).unwrap();
        assert_eq!(t0, val_a7(&es, &[]));
        // appended constraints (`NEARAIRV3_JSON`): `rb` rows 0, 1, SUM, last;
        // `rplv` on the first row of a record with `len > 0`
        let f = (0..rows)
            .find(|&q| t.cells[q * VAL_A7_WIDTH + 1] == 1 && t.cells[q * VAL_A7_WIDTH + 4] > 0)
            .unwrap();
        let h = t.height();
        let cells = [(0, 16), (1, 16), (rows, 16), (h - 1, 16), (f, 15)];
        a7_test::honest_and_tampered(4, VAL_WIDTH, &t, &cells);
    }
}
