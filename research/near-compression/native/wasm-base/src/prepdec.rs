//! E2E A-T4: honest traces of the PREP decoder-certificate tables (`WasmBase/PrepAir.lean`:
//! `CB`, `HDR`, `CODE`, `FUNC`), mirroring the reference `WasmBase/PrepDec.lean` (`hrow`,
//! `decInstr`).  Columns are addressed by name through the AIR JSON, so the layout is the Lean one.
use crate::air::TableSpec;
use crate::config::F;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use std::collections::HashMap;

fn fe(x: u64) -> F {
    F::from_u64(x)
}

/// `PrepDec.lebBytes`: at most `n` bytes, stop at the first byte `< 128`.
fn leb_bytes(c: &[u8], i: usize, n: usize) -> Option<Vec<u64>> {
    let mut out = vec![];
    for k in 0..n {
        let b = *c.get(i + k)? as u64;
        out.push(b);
        if b < 128 {
            return Some(out);
        }
    }
    None
}

fn leb_val(bs: &[u64]) -> u64 {
    bs.iter().rev().fold(0u64, |acc, &b| (b % 128) + 128 * acc)
}

/// `PrepDec.lebU`.
fn leb_u(c: &[u8], i: usize, n: usize, g: usize) -> Option<(u64, usize)> {
    let bs = leb_bytes(c, i, n)?;
    if bs.iter().skip(g).all(|b| b % 128 == 0) { Some((leb_val(&bs), bs.len())) } else { None }
}

/// `PrepDec.sval` (two's complement modulo `2^w`).
fn sval(bs: &[u64], w: usize) -> u64 {
    let mut v: u128 = 0;
    for t in 0..w {
        let bit = if t / 7 < bs.len() { (bs[t / 7] >> (t % 7)) & 1 } else { (bs[bs.len() - 1] >> 6) & 1 };
        v |= (bit as u128) << t;
    }
    v as u64
}

const NUM: &[(u64, u64)] = &[(0x45, 22), (0x67, 36), (0xA7, 1), (0xAC, 1), (0xAD, 1), (0xC0, 5)];

/// `PrepDec.clsOf`: the class number (`clsList` order) of an opcode byte.
pub fn cls_of(b: u64) -> Option<usize> {
    let num = NUM.iter().any(|&(s, n)| b >= s && b < s + n);
    let mem = b == 0x28 || b == 0x29 || (0x2C..0x36).contains(&b) || b == 0x36 || b == 0x37 || (0x3A..0x3F).contains(&b);
    Some(match b {
        0x00 | 0x1A | 0x1B => 0,
        _ if num => 0,
        0x02 | 0x03 => 1,
        0x04 => 2,
        0x05 => 3,
        0x0B => 4,
        0x0F => 5,
        0x0C | 0x0D => 6,
        0x10 => 7,
        0x20..=0x24 => 8,
        _ if mem => 9,
        0x3F | 0x40 => 10,
        0x41 => 11,
        0x42 => 12,
        _ => return None,
    })
}

/// `PrepDec.decInstr`: `(byte, immediate, length)`.
pub fn dec_instr(c: &[u8], p: usize) -> Option<(u64, u64, usize)> {
    let b = *c.get(p)? as u64;
    match cls_of(b)? {
        0 | 3 | 4 | 5 => Some((b, 0, 1)),
        1 | 2 | 10 => Some((b, 0, 2)),
        6 | 7 | 8 => leb_u(c, p + 1, 5, 3).map(|(v, l)| (b, v, 1 + l)),
        9 => {
            let a = *c.get(p + 1)?;
            if a >= 128 {
                return None;
            }
            leb_u(c, p + 2, 5, 4).map(|(v, l)| (b, v, 2 + l))
        }
        11 => leb_bytes(c, p + 1, 5).map(|bs| (b, sval(&bs, 32), 1 + bs.len())),
        _ => leb_bytes(c, p + 1, 10).map(|bs| (b, sval(&bs, 64), 1 + bs.len())),
    }
}

/// `PrepDec.HS` and one `hrow`.
#[derive(Clone, Copy, Debug)]
pub struct Hs {
    pub kind: usize,
    pub pos: usize,
    pub kk: u64,
    pub be: usize,
    pub rem: u64,
}

pub fn hrow(c: &[u8], s: Hs) -> Option<(Option<(u64, usize, usize)>, Hs)> {
    match s.kind {
        0 => {
            let id = *c.get(s.pos)?;
            let (v, l) = leb_u(c, s.pos + 1, 5, 4)?;
            if id == 10 { Some((None, Hs { kind: 1, pos: s.pos + 1 + l, ..s })) } else { Some((None, Hs { pos: s.pos + 1 + l + v as usize, ..s })) }
        }
        1 => {
            let (_, l) = leb_u(c, s.pos, 5, 4)?;
            Some((None, Hs { kind: 2, pos: s.pos + l, kk: 0, ..s }))
        }
        2 => {
            let (v, l) = leb_u(c, s.pos, 5, 4)?;
            Some((None, Hs { kind: 3, pos: s.pos + l, be: s.pos + l + v as usize, ..s }))
        }
        3 => {
            let (v, l) = leb_u(c, s.pos, 5, 4)?;
            if v == 0 {
                Some((Some((s.kk, s.pos + l, s.be)), Hs { kind: 2, pos: s.be, kk: s.kk + 1, rem: 0, ..s }))
            } else {
                Some((None, Hs { kind: 4, pos: s.pos + l, rem: v, ..s }))
            }
        }
        _ => {
            let (_, l) = leb_u(c, s.pos, 5, 4)?;
            if s.rem == 1 {
                Some((Some((s.kk, s.pos + l + 1, s.be)), Hs { kind: 2, pos: s.be, kk: s.kk + 1, rem: 0, ..s }))
            } else {
                Some((None, Hs { pos: s.pos + l + 1, rem: s.rem - 1, ..s }))
            }
        }
    }
}

/// The walk's rows up to (and including) the emission of body `kmax`.
pub fn walk(c: &[u8], kmax: u64) -> Vec<(Hs, Option<(u64, usize, usize)>)> {
    let mut s = Hs { kind: 0, pos: 8, kk: 0, be: 0, rem: 0 };
    let mut out = vec![];
    loop {
        let (e, s2) = hrow(c, s).expect("PREP walk: malformed module (the reference walk fails)");
        out.push((s, e));
        if let Some((k, _, _)) = e {
            if k == kmax {
                return out;
            }
        }
        s = s2;
    }
}

/// One function of the layout: body index, first instruction byte, body end.
#[derive(Clone, Copy, Debug)]
pub struct FnLay {
    pub k: u64,
    pub is: usize,
    pub be: usize,
}

struct Row<'a> {
    t: &'a TableSpec,
    v: Vec<F>,
}

impl<'a> Row<'a> {
    fn new(t: &'a TableSpec) -> Self {
        Row { t, v: vec![F::ZERO; t.cols.len()] }
    }
    fn s(&mut self, n: &str, x: F) {
        let i = self.t.col(n);
        self.v[i] = x;
    }
    fn u(&mut self, n: &str, x: u64) {
        self.s(n, fe(x));
    }
    /// window byte `i` (its 8 bits)
    fn byte(&mut self, i: usize, b: u64) {
        for j in 0..8 {
            self.u(&format!("y{i}b{j}"), (b >> j) & 1);
        }
    }
}

fn bytes_at(c: &[u8], p: usize, n: usize) -> Vec<u64> {
    (0..n).map(|i| c.get(p + i).map(|&b| b as u64).unwrap_or(0)).collect()
}

fn inv(x: F) -> F {
    if x == F::ZERO { F::ZERO } else { x.inverse() }
}

fn mat(rows: Vec<Vec<F>>, w: usize, h: usize) -> RowMajorMatrix<F> {
    assert!(rows.len() <= h, "PREP table needs {} rows > template {h}", rows.len());
    let mut v: Vec<F> = rows.into_iter().flatten().collect();
    v.resize(h * w, F::ZERO);
    RowMajorMatrix::new(v, w)
}

/// The decoder tables.  `code_rec` / `func_rec` are the cached records (padded to the template
/// heights; possibly tampered), `n` the live CODE rows, `lay` the FUNC rows' bodies.
pub struct DecMats {
    pub cb: RowMajorMatrix<F>,
    pub hdr: RowMajorMatrix<F>,
    pub code: RowMajorMatrix<F>,
    pub func: RowMajorMatrix<F>,
}

#[allow(clippy::too_many_arguments)]
pub fn build(
    t_cb: &TableSpec, t_hdr: &TableSpec, t_code: &TableSpec, t_func: &TableSpec, h_cb: usize, h_hdr: usize,
    code: &[u8], code_rec: &[[u64; 8]], func_rec: &[[u64; 8]], n: usize, ks: &[u64],
) -> DecMats {
    let mut lookups: HashMap<usize, u64> = HashMap::new();
    // HDR
    let kmax = *ks.iter().max().expect("a function");
    let w = walk(code, kmax);
    let mut bodies: HashMap<u64, (usize, usize, usize)> = HashMap::new(); // k -> (iS, bE, row)
    let mut hdr_rows = vec![];
    for (ri, (s, e)) in w.iter().enumerate() {
        let mut r = Row::new(t_hdr);
        let kn = ["kS", "kC", "kB", "kG", "kL"][s.kind];
        r.u("act", 1);
        r.u(kn, 1);
        r.u("pos", s.pos as u64);
        r.u("kk", s.kk);
        r.u("bE", s.be as u64);
        r.u("rem", s.rem);
        let y = bytes_at(code, s.pos, 6);
        for (i, &b) in y.iter().enumerate() {
            r.byte(i, b);
        }
        let c = |i: usize| (y[i] >> 7) & 1;
        // chain A over bytes 1..5 (aA1 = kS), chain B over 0..4 (aB0 = act − kS)
        let mut a = if s.kind == 0 { 1 } else { 0 };
        let mut reads = vec![0u64; 6];
        reads[0] = 1;
        if s.kind == 0 {
            reads[1] = 1;
        }
        for i in 2..=5 {
            a *= c(i - 1);
            r.u(&format!("aA{i}"), a);
            if s.kind == 0 {
                reads[i] = a;
            }
        }
        let mut b = if s.kind == 0 { 0 } else { 1 };
        for i in 1..=4 {
            b *= c(i - 1);
            r.u(&format!("aB{i}"), b);
            if s.kind != 0 {
                reads[i] = b;
            }
        }
        for (i, &rd) in reads.iter().enumerate() {
            r.u(&format!("u{i}"), rd);
            if rd == 1 {
                *lookups.entry(s.pos + i).or_insert(0) += 1;
            }
        }
        if s.kind == 0 {
            let d = fe(y[0]) - fe(10);
            r.u("isc", (y[0] == 10) as u64);
            r.s("zinv", inv(d));
        }
        if s.kind == 3 || s.kind == 4 {
            let ze = if s.kind == 3 { fe(leb_u(code, s.pos, 5, 4).unwrap().0) } else { fe(s.rem) - F::ONE };
            r.u("z", e.is_some() as u64);
            r.s("zi", inv(ze));
        }
        if let Some((k, is, be)) = e {
            bodies.insert(*k, (*is, *be, ri));
        }
        hdr_rows.push(r.v);
    }
    // FUNC
    let mut lay = vec![];
    let mut func_rows = vec![];
    let nf = ks.len();
    let mut offs = vec![0usize; nf + 1];
    for (i, &k) in ks.iter().enumerate() {
        let &(is, be, ri) = bodies.get(&k).expect("body emitted");
        hdr_rows[ri][t_hdr.col("mult")] += F::ONE;
        lay.push(FnLay { k, is, be });
        // size: decode the body
        let mut p = is;
        let mut sz = 0;
        while p < be {
            p += dec_instr(code, p).expect("PREP decode: instruction outside the classes").2;
            sz += 1;
        }
        assert_eq!(p, be, "body {k} does not end at its end");
        offs[i + 1] = offs[i] + sz;
    }
    assert_eq!(offs[nf], n, "FUNC layout covers the CODE records");
    for (i, fr) in func_rec.iter().enumerate() {
        let mut r = Row::new(t_func);
        for (j, &x) in fr.iter().enumerate() {
            r.v[j] = fe(x);
        }
        if i < nf {
            r.u("live", 1);
            r.u("kk", lay[i].k);
            r.u("iS", lay[i].is as u64);
            r.u("bE", lay[i].be as u64);
            r.u("size", (offs[i + 1] - offs[i]) as u64);
        }
        func_rows.push(r.v);
    }
    // CODE
    let mut code_rows = vec![];
    let mut fi = 0;
    let mut ptr = 0;
    for (j, cr) in code_rec.iter().enumerate() {
        let mut r = Row::new(t_code);
        for (q, &x) in cr.iter().enumerate() {
            r.v[q] = fe(x);
        }
        if j < n {
            while j >= offs[fi + 1] {
                fi += 1;
            }
            let l = lay[fi];
            if j == offs[fi] {
                r.u("fst", 1);
                ptr = l.is;
            }
            r.u("live", 1);
            r.u("kk", l.k);
            r.u("bE", l.be as u64);
            r.u("fsz", (offs[fi + 1] - offs[fi]) as u64);
            r.u("lpc", (j - offs[fi]) as u64);
            r.u("ptr", ptr as u64);
            let y = bytes_at(code, ptr, 11);
            for (i, &b) in y.iter().enumerate() {
                r.byte(i, b);
            }
            let k = cls_of(y[0]).expect("class");
            r.u(&format!("cls{k}"), 1);
            let c = |i: usize| (y[i] >> 7) & 1;
            let mut reads = vec![0u64; 11];
            reads[0] = 1;
            let g1 = matches!(k, 6 | 7 | 8 | 11 | 12) as u64;
            let mut a1 = vec![0u64; 11];
            a1[1] = g1;
            for i in 2..=10 {
                a1[i] = a1[i - 1] * c(i - 1);
                r.u(&format!("a1_{i}"), a1[i]);
            }
            let mut a2 = vec![0u64; 7];
            a2[2] = (k == 9) as u64;
            for i in 3..=6 {
                a2[i] = a2[i - 1] * c(i - 1);
                r.u(&format!("a2_{i}"), a2[i]);
            }
            reads[1] = a1[1] + (k == 9) as u64;
            for i in 2..=10 {
                reads[i] = a1[i] + if i <= 6 { a2[i] } else { 0 };
            }
            let mut sg = 0;
            for g in 0..10 {
                sg += a1[1 + g] * (1 - c(1 + g)) * ((y[1 + g] >> 6) & 1);
            }
            r.u("sg", sg);
            for (i, &rd) in reads.iter().enumerate() {
                assert!(rd <= 1);
                r.u(&format!("u{i}"), rd);
                if rd == 1 {
                    *lookups.entry(ptr + i).or_insert(0) += 1;
                }
            }
            ptr += dec_instr(code, ptr).expect("decode").2;
        } else {
            // padding rows: byte 0 (class eq0), no reads
            r.u("cls0", 1);
        }
        code_rows.push(r.v);
    }
    // CB
    let mut cb_rows = vec![];
    for (i, &b) in code.iter().enumerate() {
        let mut r = Row::new(t_cb);
        r.u("pos", i as u64);
        r.u("byte", b as u64);
        r.u("live", 1);
        r.u("mult", *lookups.get(&i).unwrap_or(&0));
        cb_rows.push(r.v);
    }
    assert!(lookups.keys().all(|&p| p < code.len()), "a read past the code");
    for i in code.len()..h_cb {
        let mut r = Row::new(t_cb);
        r.u("pos", i as u64);
        cb_rows.push(r.v);
    }
    DecMats {
        cb: mat(cb_rows, t_cb.cols.len(), h_cb),
        hdr: mat(hdr_rows, t_hdr.cols.len(), h_hdr),
        code: mat(code_rows, t_code.cols.len(), code_rec.len()),
        func: mat(func_rows, t_func.cols.len(), func_rec.len()),
    }
}
