//! Trace generation for all tables from the structured witness.

use crate::air::acct::AcctCols;
use crate::air::mrk::MrkCols;
use crate::air::node::NodeCols;
use crate::air::path::PathCols;
use crate::air::rcpt::{RcptCols, StrCols};
use crate::air::sha::ShaCols;
use crate::air::sha_gen::generate_trace_row_for_compression;
use crate::air::sort::SortCols;
use crate::air::{NpAir, mul_const_native};
use crate::config::Val;
use crate::consts::*;
use crate::eval::{Tally, tally_queries};
use crate::witness::{NKind, Wit};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;
use p3_sha256_air::{NUM_SHA256_COLS, SHA256_IV, Sha256Cols};
use std::borrow::{Borrow, BorrowMut};

#[inline]
fn f(x: u64) -> Val {
    Val::from_u64(x)
}

fn height_for(rows: usize, min_log: usize) -> usize {
    rows.max(1 << min_log).next_power_of_two()
}

fn le16(x: u128) -> [u8; 16] {
    x.to_le_bytes()
}

/// `a + b + cin` byte-wise with carries (carry into limb i+1 at index i).
fn add_carries(a: &[u8], b: &[u8], cin: u32) -> (Vec<u8>, Vec<u32>) {
    let n = a.len();
    let mut s = vec![0u8; n];
    let mut cs = vec![0u32; n - 1];
    let mut c = cin;
    for i in 0..n {
        let t = a[i] as u32 + b[i] as u32 + c;
        s[i] = (t & 255) as u8;
        c = t >> 8;
        if i + 1 < n {
            cs[i] = c;
        }
    }
    (s, cs)
}

fn sub_bytes(a: &[u8], b: &[u8], extra: u32) -> Vec<u8> {
    // a - b - extra (assumes non-negative)
    let mut out = vec![0u8; a.len()];
    let mut borrow: i32 = extra as i32;
    for i in 0..a.len() {
        let mut t = a[i] as i32 - b[i] as i32 - borrow;
        if t < 0 {
            t += 256;
            borrow = 1;
        } else {
            borrow = 0;
        }
        out[i] = t as u8;
    }
    assert_eq!(borrow, 0, "sub_bytes underflow");
    out
}

struct M<'a> {
    row: &'a mut [Val],
}
impl M<'_> {
    fn set(&mut self, c: usize, x: u64) {
        self.row[c] = f(x);
    }
    fn setf(&mut self, c: usize, x: Val) {
        self.row[c] = x;
    }
    fn bytes(&mut self, cols: &[usize], b: &[u8]) {
        for (i, &c) in cols.iter().enumerate() {
            self.row[c] = f(*b.get(i).unwrap_or(&0) as u64);
        }
    }
    fn u32s(&mut self, cols: &[usize], b: &[u32]) {
        for (i, &c) in cols.iter().enumerate() {
            self.row[c] = f(*b.get(i).unwrap_or(&0) as u64);
        }
    }
}

fn inv(x: Val) -> Val {
    x.try_inverse().unwrap_or(Val::ZERO)
}

/// Pad a message (FIPS 180-4) and split it into blocks of 16 big-endian words.
pub fn sha_blocks(m: &[u8]) -> Vec<[u32; 16]> {
    let mut p = m.to_vec();
    p.push(0x80);
    while p.len() % 64 != 56 {
        p.push(0);
    }
    p.extend_from_slice(&((m.len() as u64) * 8).to_be_bytes());
    p.chunks(64)
        .map(|c| core::array::from_fn(|i| u32::from_be_bytes(c[4 * i..4 * i + 4].try_into().unwrap())))
        .collect()
}

fn compress(state: &mut [u32; 8], block: &[u32; 16]) {
    let mut bytes = [0u8; 64];
    for i in 0..16 {
        bytes[4 * i..4 * i + 4].copy_from_slice(&block[i].to_be_bytes());
    }
    #[allow(deprecated)]
    let ga = sha2::digest::generic_array::GenericArray::clone_from_slice(&bytes);
    sha2::compress256(state, &[ga]);
}

pub fn sha_trace(c: &ShaCols, msgs: &[(u32, Vec<u8>, [u8; 32])]) -> RowMajorMatrix<Val> {
    struct RowIn {
        input: [u32; 24],
        msg: u32,
        blk: u32,
        first: bool,
        last: bool,
        cnt: u32,
        seen: bool,
        p80: bool,
        d: u32,
        act: bool,
    }
    let mut rows: Vec<RowIn> = Vec::new();
    for (id, m, _) in msgs {
        let blocks = sha_blocks(m);
        let l = m.len() as u32;
        let mut h = SHA256_IV;
        let nb = blocks.len();
        for (bi, blk) in blocks.iter().enumerate() {
            let mut input = [0u32; 24];
            input[..16].copy_from_slice(blk);
            input[16..].copy_from_slice(&h);
            let start = 64 * bi as u32;
            rows.push(RowIn {
                input,
                msg: *id,
                blk: bi as u32,
                first: bi == 0,
                last: bi + 1 == nb,
                cnt: start.min(l),
                seen: l / 64 < bi as u32,
                p80: l / 64 == bi as u32,
                d: l.saturating_sub(start).min(64),
                act: true,
            });
            compress(&mut h, blk);
        }
    }
    let n = rows.len();
    let height = height_for(n, 2);
    for _ in n..height {
        let mut input = [0u32; 24];
        input[16..].copy_from_slice(&SHA256_IV);
        rows.push(RowIn {
            input,
            msg: 0,
            blk: 0,
            first: false,
            last: false,
            cnt: 0,
            seen: false,
            p80: false,
            d: 0,
            act: false,
        });
    }
    let w = c.width;
    let mut values = Val::zero_vec(height * w);
    values.par_chunks_mut(w).zip(rows.par_iter()).for_each(|(row, ri)| {
        {
            let sha: &mut Sha256Cols<Val> = row[..NUM_SHA256_COLS].borrow_mut();
            generate_trace_row_for_compression(sha, ri.input);
        }
        if ri.act {
            let mut m = M { row };
            m.set(c.act, 1);
            m.set(c.first, ri.first as u64);
            m.set(c.last, ri.last as u64);
            m.set(c.msg, ri.msg as u64);
            m.set(c.blk, ri.blk as u64);
            m.set(c.cnt, ri.cnt as u64);
            m.set(c.seen, ri.seen as u64);
            m.set(c.p80, ri.p80 as u64);
            m.set(c.pn, (ri.p80 && !ri.last) as u64);
            for kk in 0..64 {
                m.set(c.f[kk], ((kk as u32) < ri.d) as u64);
            }
        }
    });
    RowMajorMatrix::new(values, w)
}

fn set_str(m: &mut M<'_>, s: &StrCols, id: &[u8]) {
    for i in 0..64 {
        let act = i < id.len();
        m.set(s.a[i], act as u64);
        m.set(s.c[i], if act { id[i] as u64 } else { 0 });
        m.set(s.cls[i], if act { char_class(id[i]) as u64 } else { 0 });
    }
}

pub fn rcpt_trace(c: &RcptCols, wit: &Wit) -> RowMajorMatrix<Val> {
    let n = wit.receipts.len();
    let height = height_for(n, 2);
    let w = c.width;
    let mut values = Val::zero_vec(height * w);
    let bgp = wit.claim.block_gas_price;
    let mut prev_tok = 0u128;
    for (r, rw) in wit.receipts.iter().enumerate() {
        let mut m = M { row: &mut values[r * w..(r + 1) * w] };
        m.set(c.act, 1);
        m.set(c.isf, (r == 0) as u64);
        m.set(c.lastr, (r + 1 == n) as u64);
        m.set(c.r, r as u64);
        m.set(c.o, rw.o as u64);
        m.set(c.o2, rw.o2 as u64);
        set_str(&mut m, &c.sp, &rw.pred);
        set_str(&mut m, &c.sv, &rw.recv);
        set_str(&mut m, &c.ss, &rw.signer);
        let hexc = rw.recv.iter().filter(|&&x| char_class(x) == 1).count() as u64;
        let hexc2 = rw.recv.iter().skip(2).filter(|&&x| char_class(x) == 1).count() as u64;
        m.set(c.hexcnt, hexc);
        m.set(c.hexcnt2, hexc2);
        let sq = |x: i64| (x * x) as u64;
        let lp = rw.pred.len() as i64;
        let mut sys = sq(lp - 6);
        for (i, &ch) in crate::air::rcpt::SYSTEM.iter().enumerate() {
            sys += sq(*rw.pred.get(i).unwrap_or(&0) as i64 - ch as i64);
        }
        m.setf(c.inv_sys, inv(f(sys)));
        let lv = rw.recv.len() as i64;
        let p1 = sq(lv - 64) + sq(hexc as i64 - lv);
        m.setf(c.inv_n[0], inv(f(p1)));
        for (j, second) in [(1usize, b'x'), (2, b's')] {
            let p = sq(lv - 42)
                + sq(rw.recv[0] as i64 - b'0' as i64)
                + sq(rw.recv[1] as i64 - second as i64)
                + sq(hexc2 as i64 - 40);
            m.setf(c.inv_n[j], inv(f(p)));
        }
        m.bytes(&c.rid, &rw.rid);
        m.set(c.kt, rw.kt as u64);
        m.bytes(&c.pk, &rw.pk);
        m.bytes(&c.gp, &le16(rw.gp));
        m.bytes(&c.dep, &le16(rw.dep));
        m.set(c.hr, rw.hr as u64);
        let d = le16(rw.d);
        m.bytes(&c.d, &d);
        let (y, _x) = if rw.hr { (le16(bgp), le16(rw.gp)) } else { (le16(rw.gp), le16(bgp)) };
        let (_s, cd) = add_carries(&y, &d, 0);
        m.u32s(&c.cd, &cd);
        let dsum: u64 = d.iter().map(|&x| x as u64).sum();
        m.setf(c.dinv, if rw.hr { inv(f(dsum)) } else { Val::ZERO });
        let (burnt, cb) = mul_const_native(&y, &G_BYTES, 16).expect("burnt overflow");
        assert_eq!(burnt, le16(rw.burnt));
        m.bytes(&c.burnt, &burnt);
        m.u32s(&c.cb, &cb);
        let surplus = if rw.hr { d } else { [0u8; 16] };
        let (ramt, cr) = mul_const_native(&surplus, &G_BYTES, 16).expect("refund overflow");
        m.bytes(&c.ramt, &ramt);
        m.u32s(&c.cr, &cr);
        m.bytes(&c.t, &le16(rw.tok));
        if r > 0 {
            let (_s, ct) = add_carries(&le16(prev_tok), &burnt, 0);
            m.u32s(&c.ct, &ct);
        }
        prev_tok = rw.tok;
        m.set(c.rf, rw.rf as u64);
        m.bytes(&c.refund_id, &rw.refund_id);
        m.bytes(&c.peo_dig, &rw.peo_dig);
        m.set(c.kacc, rw.k as u64);
        let locked = le16(rw.locked);
        m.bytes(&c.locked, &locked);
        let storage = rw.storage.to_le_bytes();
        m.bytes(&c.storage, &storage);
        m.set(c.t_prev, rw.t_prev as u64);
        let abef = le16(rw.abef);
        let aaft = le16(rw.aaft);
        m.bytes(&c.abef, &abef);
        m.bytes(&c.aaft, &aaft);
        let (_s, ca) = add_carries(&abef, &le16(rw.dep), 0);
        m.u32s(&c.ca, &ca);
        let (tot, ctot) = add_carries(&aaft, &locked, 0);
        m.bytes(&c.tot, &tot);
        m.u32s(&c.ctot, &ctot);
        let notmax: u64 = aaft.iter().map(|&x| 255 - x as u64).sum();
        m.setf(c.inv_max, inv(f(notmax)));
        let (q, cq) = mul_const_native(&storage, &STORAGE_PRICE_BYTES, 16).expect("storage price");
        m.bytes(&c.q, &q);
        m.u32s(&c.cq, &cq);
        let sz = rw.storage <= 770;
        m.set(c.sz, sz as u64);
        if !sz {
            let e = sub_bytes(&tot, &q, 0);
            let (_s, ce) = add_carries(&q, &e, 0);
            m.bytes(&c.e, &e);
            m.u32s(&c.ce, &ce);
        }
    }
    RowMajorMatrix::new(values, w)
}

pub fn mrk_trace(c: &MrkCols, wit: &Wit) -> RowMajorMatrix<Val> {
    let n = wit.mrk.len();
    let height = height_for(n, 2);
    let w = c.width;
    let mut values = Val::zero_vec(height * w);
    for row in 0..height {
        let mut m = M { row: &mut values[row * w..(row + 1) * w] };
        m.set(c.idx, row as u64);
        m.set(c.isf, (row == 0) as u64);
        if let Some(x) = wit.mrk.get(row) {
            m.set(c.act, 1);
            m.set(c.j, x.j as u64);
            m.set(c.i, x.i as u64);
            m.set(c.sp, x.sp as u64);
            m.set(c.s, x.s as u64);
            m.set(c.odd, x.odd as u64);
            m.set(c.lil, x.lil as u64);
            m.set(c.root, x.root as u64);
            m.setf(c.rinv, if x.s == 1 { Val::ZERO } else { inv(f(x.s as u64 - 1)) });
            m.set(c.msg_l, x.msg_l as u64);
            m.set(c.msg_r, x.msg_r as u64);
            m.set(c.own, x.own as u64);
            if !(x.odd && x.lil) {
                m.bytes(&c.l, &x.l);
                m.bytes(&c.rr, &x.r);
            }
        }
    }
    RowMajorMatrix::new(values, w)
}

pub fn sort_trace(c: &SortCols, wit: &Wit) -> RowMajorMatrix<Val> {
    let n = wit.sorted_rids.len();
    let height = height_for(n, 2);
    let w = c.width;
    let mut values = Val::zero_vec(height * w);
    for (t, rid) in wit.sorted_rids.iter().enumerate() {
        let mut m = M { row: &mut values[t * w..(t + 1) * w] };
        m.set(c.act, 1);
        m.set(c.isf, (t == 0) as u64);
        m.bytes(&c.rid, rid);
        if t > 0 {
            let prev = &wit.sorted_rids[t - 1];
            let diff = sub_bytes(rid, prev, 1);
            let (s, cs) = add_carries(prev, &diff, 1);
            assert_eq!(&s[..], &rid[..]);
            m.bytes(&c.diff, &diff);
            m.u32s(&c.cs, &cs);
        }
    }
    RowMajorMatrix::new(values, w)
}

pub fn acct_trace(c: &AcctCols, wit: &Wit) -> RowMajorMatrix<Val> {
    let n = wit.accounts.len();
    let height = height_for(n, 2);
    let w = c.width;
    let mut values = Val::zero_vec(height * w);
    for (k, a) in wit.accounts.iter().enumerate() {
        let mut m = M { row: &mut values[k * w..(k + 1) * w] };
        m.set(c.act, 1);
        m.set(c.isf, (k == 0) as u64);
        m.set(c.k, k as u64);
        for i in 0..64 {
            let on = i < a.id.len();
            let ch = if on { a.id[i] } else { 0 };
            m.set(c.a[i], on as u64);
            m.set(c.c[i], ch as u64);
            m.set(c.hi[i], if on { (ch >> 4) as u64 } else { 0 });
            m.set(c.lo[i], if on { (ch & 15) as u64 } else { 0 });
        }
        m.bytes(&c.val, &a.val);
        m.bytes(&c.post, &le16(a.post_amt));
        m.set(c.o, a.owner as u64);
        m.set(c.io, a.iterm as u64);
        m.set(c.t_last, a.t_last as u64);
        let notmax: u64 = a.val[..16].iter().map(|&x| 255 - x as u64).sum();
        m.setf(c.inv_max, inv(f(notmax)));
    }
    RowMajorMatrix::new(values, w)
}

pub fn node_trace(c: &NodeCols, wit: &Wit) -> RowMajorMatrix<Val> {
    let n = wit.nodes.len();
    let height = height_for(n, 2);
    let w = c.width;
    let mut values = Val::zero_vec(height * w);
    let mut ssum: u64 = 0;
    for (id, nd) in wit.nodes.iter().enumerate() {
        let mut m = M { row: &mut values[id * w..(id + 1) * w] };
        m.set(c.act, 1);
        m.set(c.isf, (id == 0) as u64);
        m.set(c.lastn, (id + 1 == n) as u64);
        m.set(c.nid, id as u64);
        let (tl, te, tb1, tb2) = (
            nd.kind == NKind::Leaf,
            nd.kind == NKind::Ext,
            nd.kind == NKind::B1,
            nd.kind == NKind::B2,
        );
        m.set(c.tl, tl as u64);
        m.set(c.te, te as u64);
        m.set(c.tb1, tb1 as u64);
        m.set(c.tb2, tb2 as u64);
        m.set(c.odd, nd.odd as u64);
        m.set(c.x0, nd.x0 as u64);
        for (mi, &kb) in nd.keybytes.iter().enumerate() {
            m.set(c.kb[mi], 1);
            m.set(c.khi[mi], (kb >> 4) as u64);
            m.set(c.klo[mi], (kb & 15) as u64);
        }
        m.set(c.s, nd.s() as u64);
        if tl || tb2 {
            m.bytes(&c.vlen, &nd.vlen);
            m.bytes(&c.vh, &nd.vh);
            let post_vh = match nd.touched {
                Some(k) => {
                    let a = &wit.accounts[k];
                    let mut v = a.val;
                    v[..16].copy_from_slice(&a.post_amt.to_le_bytes());
                    crate::sha256(&v)
                }
                None => nd.vh,
            };
            m.bytes(&c.pvh, &post_vh);
        }
        if let Some(k) = nd.touched {
            m.set(c.tv, 1);
            m.set(c.vk, k as u64);
        }
        for j in 0..16 {
            m.set(c.bm[j], (nd.bm >> j & 1) as u64);
            if let Some(h) = nd.child_hash[j] {
                m.bytes(&c.w[j], &h);
                match nd.cid[j] {
                    Some(cid) => {
                        m.set(c.rv[j], 1);
                        m.set(c.cid[j], cid as u64);
                        m.bytes(&c.pw[j], &wit.nodes[cid].post_dig);
                    }
                    None => m.bytes(&c.pw[j], &h),
                }
            }
        }
        m.bytes(&c.mem, &nd.mem);
        let hplen = 1 + nd.keybytes.len() as u64;
        let pop = nd.bm.count_ones() as u64;
        let pv_ = if tl { 5 + hplen } else if tb2 { 1 } else { 0 };
        let pc = if te { 5 + hplen } else if tb1 { 3 } else if tb2 { 39 } else { 0 };
        let pm = match nd.kind {
            NKind::Leaf => 5 + hplen + 36,
            NKind::Ext => 5 + hplen + 32,
            NKind::B1 => 3 + 32 * pop,
            NKind::B2 => 39 + 32 * pop,
        };
        assert_eq!(pm + 8, nd.pre.len() as u64, "node layout");
        m.set(c.pv_, pv_);
        m.set(c.pc, pc);
        m.set(c.pm, pm);
        ssum += pm + 8 + if nd.touched.is_some() { 72 } else { 0 };
        m.set(c.ssum, ssum);
        if id + 1 == n {
            let slack = MAX_WITNESS_BYTES as u64 - ssum;
            m.bytes(&c.wsd, &slack.to_le_bytes()[..3]);
        }
    }
    RowMajorMatrix::new(values, w)
}

pub fn path_trace(c: &PathCols, wit: &Wit) -> RowMajorMatrix<Val> {
    let n = wit.paths.len();
    let height = height_for(n, 2);
    let w = c.width;
    let mut values = Val::zero_vec(height * w);
    for (t, p) in wit.paths.iter().enumerate() {
        let mut m = M { row: &mut values[t * w..(t + 1) * w] };
        m.set(c.act, 1);
        m.set(c.isf, (t == 0) as u64);
        m.set(c.start, p.start as u64);
        m.set(c.end, p.end as u64);
        m.set(c.k, p.k as u64);
        m.set(c.t, p.t as u64);
        m.set(c.nib, p.nib as u64);
        m.set(c.n, p.n as u64);
        m.set(c.i, p.i as u64);
        m.set(c.n2, p.n2 as u64);
        m.set(c.i2, p.i2 as u64);
        m.set(c.jump, p.jump as u64);
        m.set(c.n3, p.n3 as u64);
        m.set(c.i3, p.i3 as u64);
    }
    RowMajorMatrix::new(values, w)
}

/// Generate every trace (provider multiplicities zero).
pub fn all_traces(airs: &[NpAir], wit: &Wit) -> Vec<RowMajorMatrix<Val>> {
    let mut out = Vec::with_capacity(airs.len());
    for a in airs {
        let t = match a {
            NpAir::Sha(s) => sha_trace(&s.c, &wit.msgs),
            NpAir::Rcpt(s) => rcpt_trace(&s.c, wit),
            NpAir::Mrk(s) => mrk_trace(&s.c, wit),
            NpAir::Sort(s) => sort_trace(&s.c, wit),
            NpAir::Acct(s) => acct_trace(&s.c, wit),
            NpAir::Node(s) => node_trace(&s.c, wit),
            NpAir::Path(s) => path_trace(&s.c, wit),
            NpAir::Byte(_) => RowMajorMatrix::new(Val::zero_vec(256 * 3), 3),
            NpAir::U16(_) => RowMajorMatrix::new(Val::zero_vec(65536), 1),
        };
        out.push(t);
    }
    out
}

fn u(x: Val) -> u32 {
    x.as_canonical_u32()
}

/// Recompute every provider multiplicity from the consumers' queries.
/// Reads the provided tuples from the trace itself (so it also serves the
/// witness-mutation tool).
pub fn fill_multiplicities(airs: &[NpAir], traces: &mut [RowMajorMatrix<Val>], pvs: &[Val]) {
    let mut tally = Tally::default();
    for (a, t) in airs.iter().zip(traces.iter()) {
        if matches!(a, NpAir::Sha(_) | NpAir::Byte(_) | NpAir::U16(_)) {
            continue;
        }
        let pv: &[Val] = if a.num_pv() > 0 { pvs } else { &[] };
        let h = t.height();
        // parallel tally in chunks
        let parts: Vec<Tally> = (0..h)
            .into_par_iter()
            .chunks(256)
            .map(|rows| {
                let mut tl = Tally::default();
                let lo = rows[0];
                let hi = *rows.last().unwrap() + 1;
                // provider columns are irrelevant for queries: evaluate with current trace
                tally_queries(a, t, pv, lo..hi, &mut tl);
                tl
            })
            .collect();
        for p in parts {
            for (k, v) in p.0 {
                *tally.0.entry(k).or_insert(0) += v;
            }
        }
    }
    // SHA rows query RANGE nothing; but the SHA table has no lookup queries.
    for (a, t) in airs.iter().zip(traces.iter_mut()) {
        let w = t.width();
        match a {
            NpAir::Sha(s) => {
                let c = &s.c;
                t.values.par_chunks_mut(w).for_each(|row| {
                    if row[c.last] != Val::ONE {
                        return;
                    }
                    let sha: &Sha256Cols<Val> = row[..NUM_SHA256_COLS].borrow();
                    let mut tup = vec![u(row[c.msg])];
                    for i in 0..8 {
                        let mut lo = 0u32;
                        let mut hi = 0u32;
                        for b in (0..16).rev() {
                            lo = lo * 2 + u(sha.h_out[i][b]);
                            hi = hi * 2 + u(sha.h_out[i][16 + b]);
                        }
                        tup.push(hi);
                        tup.push(lo);
                    }
                    let m = tally.get(BUS_DIGEST, &tup);
                    row[c.dm] = f(m);
                });
            }
            NpAir::Rcpt(s) => {
                let c = &s.c;
                for row in t.values.chunks_mut(w) {
                    if row[c.act] != Val::ONE {
                        continue;
                    }
                    let r = u(row[c.r]);
                    let tup = [0, r, msg_id(K_LEAF, 0) + r];
                    row[c.m_leaf] = f(tally.get(BUS_MPOS, &tup));
                }
            }
            NpAir::Mrk(s) => {
                let c = &s.c;
                for row in t.values.chunks_mut(w) {
                    if row[c.act] != Val::ONE {
                        continue;
                    }
                    let tup = [u(row[c.j]), u(row[c.i]), u(row[c.own])];
                    row[c.m_prov] = f(tally.get(BUS_MPOS, &tup));
                }
            }
            NpAir::Acct(s) => {
                let c = &s.c;
                for row in t.values.chunks_mut(w) {
                    if row[c.act] != Val::ONE {
                        continue;
                    }
                    let len: u32 = c.a.iter().map(|&i| u(row[i])).sum();
                    let mut tup = vec![u(row[c.k]), len];
                    for j in 0..PACK_LIMBS {
                        let mut acc = 0u32;
                        for tt in (0..3).rev() {
                            let idx = 3 * j + tt;
                            let x = if idx < 64 { u(row[c.c[idx]]) } else { 0 };
                            acc = acc.wrapping_mul(256).wrapping_add(x);
                        }
                        tup.push((Val::from_u32(acc)).as_canonical_u32());
                    }
                    for i in 16..32 {
                        tup.push(u(row[c.val[i]]));
                    }
                    for i in 64..72 {
                        tup.push(u(row[c.val[i]]));
                    }
                    row[c.m_acct] = f(tally.get(BUS_ACCT, &tup));
                }
            }
            NpAir::Node(s) => {
                let c = &s.c;
                for row in t.values.chunks_mut(w) {
                    if row[c.act] != Val::ONE {
                        continue;
                    }
                    let nid = u(row[c.nid]);
                    for j in 0..16 {
                        let tup = [nid, 0, j as u32, u(row[c.cid[j]]), 0];
                        row[c.me[j]] = f(tally.get(BUS_EDGE, &tup));
                    }
                    let first = if u(row[c.odd]) == 1 {
                        Some(u(row[c.x0]))
                    } else if u(row[c.kb[0]]) == 1 {
                        Some(u(row[c.khi[0]]))
                    } else {
                        None
                    };
                    row[c.m_nib] = match first {
                        Some(x) => f(tally.get(BUS_EDGE, &[nid, 0, x, nid, 1])),
                        None => Val::ZERO,
                    };
                    let tup = [nid, u(row[c.s]), u(row[c.cid[0]]), 0];
                    row[c.m_eps] = f(tally.get(BUS_EPS, &tup));
                }
            }
            NpAir::Byte(_) => {
                for x in 0..256u32 {
                    let row = &mut t.values[x as usize * 3..x as usize * 3 + 3];
                    row[0] = f(tally.get(BUS_RANGE8, &[x]));
                    row[1] = f(tally.get(BUS_CLASS, &[x, char_class(x as u8) as u32]));
                    row[2] = f(tally.get(BUS_NIB, &[x, x >> 4, x & 15]));
                }
            }
            NpAir::U16(_) => {
                t.values.par_iter_mut().enumerate().for_each(|(x, v)| {
                    *v = f(tally.get(BUS_RANGE16, &[x as u32]));
                });
            }
            _ => {}
        }
    }
}

pub fn pv_vals(pv: &[u8]) -> Vec<Val> {
    pv.iter().map(|&b| f(b as u64)).collect()
}
