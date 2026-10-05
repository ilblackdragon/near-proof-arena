//! SHA-256 toy (milestone M1, second toy): lane L5's SHA-256 block table
//! (`ZkFormal.Sha.{Layout,Table,Gen}`) plus two companion tables, and the
//! honest trace generator.
//!
//! * [`sha_table`] mirrors `ZkFormal.Sha.Table.table` **term for term** (same
//!   constraint order, same expression trees), followed by the generated
//!   multiplicity-bit constraints, so `npudr export sha` is byte-identical to
//!   `np-lean-export sha` (conformance/Conformance/Sha.lean).
//! * [`sha_trace`] mirrors `ZkFormal.Sha.Gen.honestCell` cell by cell (checked
//!   against `np-lean-shatrace` by conformance/run.sh).
//! * Companions (Conformance/Sha.lean): `bytes` (width 4: `Id, pos, byte, s`)
//!   sends `(Id, pos, byte)` on bus 0; `digest` (width 35: `Id, len, d0..d31,
//!   s`) receives `(Id, len, d0..d31)` on bus 1.

use p3_matrix::dense::RowMajorMatrix;
use rayon::prelude::*;
use sha2::{Digest, Sha256};

use crate::air::{Air, Expr, Interaction, Table};
use crate::field::F;

// ---------------------------------------------------------------------------
// Layout (ZkFormal.Sha.Layout)
// ---------------------------------------------------------------------------

pub const WIDTH: usize = 544;
pub fn col_a(i: usize, b: usize) -> usize { 32 * i + b }
pub fn col_e(i: usize, b: usize) -> usize { 128 + 32 * i + b }
pub fn col_w(i: usize, b: usize) -> usize { 256 + 32 * i + b }
pub fn col_ca(i: usize, l: usize, k: usize) -> usize { 384 + 6 * i + 3 * l + k }
pub fn col_ce(i: usize, l: usize, k: usize) -> usize { 408 + 6 * i + 3 * l + k }
pub fn col_cw(i: usize, l: usize, k: usize) -> usize { 432 + 6 * i + 3 * l + k }
pub fn col_i4(i: usize, l: usize) -> usize { 456 + 2 * i + l }
pub fn col_i8(i: usize, l: usize) -> usize { 464 + 2 * i + l }
pub fn col_i12(i: usize, l: usize) -> usize { 472 + 2 * i + l }
pub fn col_w3(i: usize, l: usize) -> usize { 480 + 2 * i + l }
pub fn col_hin(w: usize, l: usize) -> usize { 486 + 2 * w + l }
pub fn col_r(j: usize) -> usize { 502 + j }
pub const COL_D: usize = 518;
pub const COL_S: usize = 519;
pub fn col_f(k: usize) -> usize { 520 + k }
pub const COL_FPREV: usize = 536;
pub const COL_ND: usize = 537;
pub const COL_ID: usize = 538;
pub const COL_LAST: usize = 539;
pub const COL_P80: usize = 540;
pub const COL_SEEN: usize = 541;
pub const COL_PN: usize = 542;
pub const COL_DMULT: usize = 543;

pub fn col_st(w: usize, b: usize) -> usize { if w < 4 { col_a(3 - w, b) } else { col_e(7 - w, b) } }
pub fn col_cst(w: usize, l: usize, k: usize) -> usize {
    if w < 4 { col_ca(3 - w, l, k) } else { col_ce(7 - w, l, k) }
}
fn bool_cols() -> Vec<usize> {
    let mut v: Vec<usize> = (0..456).collect();
    v.extend(502..536);
    v.extend([COL_FPREV, COL_LAST, COL_P80, COL_SEEN]);
    v
}

pub const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98,
    0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8,
    0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
    0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
    0xc67178f2,
];
pub const H0: [u32; 8] =
    [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];

// ---------------------------------------------------------------------------
// Expression builders (namespace `E` of ZkFormal.Sha.Table)
// ---------------------------------------------------------------------------

fn c(x: usize) -> Expr { Expr::Col(x, false) }
fn n(x: usize) -> Expr { Expr::Col(x, true) }
fn k(v: u64) -> Expr { Expr::Const(v) }
fn add(a: Expr, b: Expr) -> Expr { Expr::add(a, b) }
fn mul(a: Expr, b: Expr) -> Expr { Expr::mul(a, b) }
fn sub(a: Expr, b: Expr) -> Expr { Expr::add(a, Expr::neg(b)) }
/// `sum [] = 0`, `sum (e :: es) = e + sum es` (right-nested, ends in `0`).
fn sum(es: Vec<Expr>) -> Expr {
    es.into_iter().rev().fold(k(0), |acc, e| add(e, acc))
}
fn smul(v: u64, e: Expr) -> Expr { mul(k(v), e) }
fn not(x: Expr) -> Expr { sub(k(1), x) }
fn xor2(x: Expr, y: Expr) -> Expr { sub(add(x.clone(), y.clone()), smul(2, mul(x, y))) }
fn xor3(x: Expr, y: Expr, z: Expr) -> Expr { xor2(xor2(x, y), z) }
fn ch(x: Expr, y: Expr, z: Expr) -> Expr { add(mul(x.clone(), y), mul(not(x), z)) }
fn maj(x: Expr, y: Expr, z: Expr) -> Expr {
    sub(
        add(add(mul(x.clone(), y.clone()), mul(x.clone(), z.clone())), mul(y.clone(), z.clone())),
        smul(2, mul(mul(x, y), z)),
    )
}
fn bits(x: &dyn Fn(usize) -> Expr, off: usize, len: usize) -> Expr {
    sum((0..len).map(|b| smul(1u64 << b, x(off + b))).collect())
}
fn limb(x: &dyn Fn(usize) -> Expr, l: usize) -> Expr { bits(x, 16 * l, 16) }
fn sig(x: &dyn Fn(usize) -> Expr, r1: usize, r2: usize, r3: usize, shr: bool, b: usize) -> Expr {
    let third = if shr {
        if b + r3 < 32 { x(b + r3) } else { k(0) }
    } else {
        x((b + r3) % 32)
    };
    xor3(x((b + r1) % 32), x((b + r2) % 32), third)
}
fn add_c(gate: Expr, terms: Vec<Expr>, cin: Expr, res: Expr, cout: Expr) -> Expr {
    mul(gate, sub(add(sum(terms), cin), add(res, smul(65536, cout))))
}
fn eq_g(gate: Expr, x: Expr, y: Expr) -> Expr { mul(gate, sub(x, y)) }

fn win_a(u: usize, b: usize) -> Expr { if u < 4 { c(col_a(u, b)) } else { n(col_a(u - 4, b)) } }
fn win_e(u: usize, b: usize) -> Expr { if u < 4 { c(col_e(u, b)) } else { n(col_e(u - 4, b)) } }
fn carry_n(cc: fn(usize, usize, usize) -> usize, i: usize, l: usize) -> Expr {
    bits(&|kk| n(cc(i, l, kk)), 0, 3)
}
fn kind_n(js: impl Iterator<Item = usize>) -> Expr { sum(js.map(|j| n(col_r(j))).collect()) }
fn kind_c(js: impl Iterator<Item = usize>) -> Expr { sum(js.map(|j| c(col_r(j))).collect()) }
fn g_round() -> Expr { kind_n(0..16) }
fn g_sched() -> Expr { kind_n(4..16) }
fn g_help() -> Expr { kind_n(1..16) }
fn g_msg_c() -> Expr { kind_c(0..4) }
fn k_limb(i: usize, l: usize) -> Expr {
    sum((0..16).map(|j| mul(n(col_r(j)), k(((K[4 * j + i] as u64) >> (16 * l)) % 65536))).collect())
}

fn bool_c(x: usize) -> Expr { mul(c(x), sub(c(x), k(1))) }

fn c_kind() -> Vec<Expr> {
    let flag_sum = || sum((0..16).map(col_r).chain([COL_D, COL_S]).map(c).collect());
    let mut v = vec![mul(flag_sum(), sub(flag_sum(), k(1)))];
    v.extend((0..15).map(|j| sub(n(col_r(j + 1)), c(col_r(j)))));
    v.push(sub(n(COL_D), c(col_r(15))));
    v.push(sub(n(col_r(0)), sub(add(c(COL_S), c(COL_D)), mul(c(COL_D), c(COL_LAST)))));
    v.push(mul(Expr::IsFirst, add(kind_c(0..16), c(COL_D))));
    v
}

fn c_iv() -> Vec<Expr> {
    let mut v = vec![];
    for w in 0..8 {
        for b in 0..32 {
            v.push(eq_g(c(COL_S), c(col_st(w, b)), k(((H0[w] >> b) & 1) as u64)));
        }
    }
    v
}

fn ch_e(i: usize) -> impl Fn(usize) -> Expr {
    move |b| ch(win_e(i + 3, b), win_e(i + 2, b), win_e(i + 1, b))
}

fn round_a(i: usize, l: usize) -> Expr {
    add_c(
        g_round(),
        vec![
            limb(&|b| win_e(i, b), l),
            limb(&|b| sig(&|x| win_e(i + 3, x), 6, 11, 25, false, b), l),
            limb(&ch_e(i), l),
            k_limb(i, l),
            limb(&|b| n(col_w(i, b)), l),
            limb(&|b| sig(&|x| win_a(i + 3, x), 2, 13, 22, false, b), l),
            limb(&|b| maj(win_a(i + 3, b), win_a(i + 2, b), win_a(i + 1, b)), l),
        ],
        if l == 0 { k(0) } else { carry_n(col_ca, i, 0) },
        limb(&|b| n(col_a(i, b)), l),
        carry_n(col_ca, i, l),
    )
}

fn round_e(i: usize, l: usize) -> Expr {
    add_c(
        g_round(),
        vec![
            limb(&|b| win_a(i, b), l),
            limb(&|b| win_e(i, b), l),
            limb(&|b| sig(&|x| win_e(i + 3, x), 6, 11, 25, false, b), l),
            limb(&ch_e(i), l),
            k_limb(i, l),
            limb(&|b| n(col_w(i, b)), l),
        ],
        if l == 0 { k(0) } else { carry_n(col_ce, i, 0) },
        limb(&|b| n(col_e(i, b)), l),
        carry_n(col_ce, i, l),
    )
}

fn w2(i: usize, b: usize) -> Expr { if i < 2 { c(col_w(i + 2, b)) } else { n(col_w(i - 2, b)) } }
fn w7(i: usize, l: usize) -> Expr { if i < 3 { c(col_w3(i, l)) } else { limb(&|b| c(col_w(0, b)), l) } }
fn w15(i: usize, b: usize) -> Expr { if i < 3 { c(col_w(i + 1, b)) } else { n(col_w(0, b)) } }

fn sched(i: usize, l: usize) -> Expr {
    add_c(
        g_sched(),
        vec![limb(&|b| sig(&|x| w2(i, x), 17, 19, 10, true, b), l), w7(i, l), c(col_i12(i, l))],
        if l == 0 { k(0) } else { carry_n(col_cw, i, 0) },
        limb(&|b| n(col_w(i, b)), l),
        carry_n(col_cw, i, l),
    )
}

fn c_help() -> Vec<Expr> {
    let mut v = vec![];
    for i in 0..4 {
        for l in 0..2 {
            v.push(eq_g(
                g_help(),
                n(col_i4(i, l)),
                add(limb(&|b| sig(&|x| w15(i, x), 7, 18, 3, true, b), l), limb(&|b| c(col_w(i, b)), l)),
            ));
            v.push(eq_g(g_help(), n(col_i8(i, l)), c(col_i4(i, l))));
            v.push(eq_g(g_help(), n(col_i12(i, l)), c(col_i8(i, l))));
        }
    }
    for i in 0..3 {
        for l in 0..2 {
            v.push(eq_g(g_help(), n(col_w3(i, l)), limb(&|b| c(col_w(i + 1, b)), l)));
        }
    }
    for w in 0..8 {
        for l in 0..2 {
            v.push(eq_g(g_help(), n(col_hin(w, l)), c(col_hin(w, l))));
            v.push(eq_g(n(col_r(0)), n(col_hin(w, l)), limb(&|b| c(col_st(w, b)), l)));
        }
    }
    v
}

fn c_digest() -> Vec<Expr> {
    let mut v = vec![];
    for w in 0..8 {
        for l in 0..2 {
            v.push(add_c(
                n(COL_D),
                vec![c(col_hin(w, l)), limb(&|b| c(col_st(w, b)), l)],
                if l == 0 { k(0) } else { bits(&|kk| n(col_cst(w, 0, kk)), 0, 3) },
                limb(&|b| n(col_st(w, b)), l),
                bits(&|kk| n(col_cst(w, l, kk)), 0, 3),
            ));
        }
    }
    v
}

fn byte_e(q: usize) -> Expr { bits(&|b| c(col_w(q / 4, b)), 8 * (3 - q % 4), 8) }
fn drop_e(q: usize) -> Expr { sub(if q == 0 { c(COL_FPREV) } else { c(col_f(q - 1)) }, c(col_f(q))) }
fn f_sum_c() -> Expr { sum((0..16).map(|q| c(col_f(q))).collect()) }
fn f_sum_n() -> Expr { sum((0..16).map(|q| n(col_f(q))).collect()) }

fn c_frame() -> Vec<Expr> {
    let g_block_n = || add(g_round(), n(COL_D));
    let g_inner_n = || add(g_help(), n(COL_D));
    let r = |j| c(col_r(j));
    let mut v: Vec<Expr> = (0..15).map(|q| mul(c(col_f(q + 1)), not(c(col_f(q))))).collect();
    v.push(mul(c(col_f(0)), not(c(COL_FPREV))));
    v.push(mul(not(g_msg_c()), c(col_f(0))));
    v.push(mul(c(col_r(0)), not(c(COL_FPREV))));
    v.extend((1..4).map(|j| eq_g(n(col_r(j)), n(COL_FPREV), c(col_f(15)))));
    v.extend([
        eq_g(g_block_n(), n(COL_ND), add(mul(not(c(COL_S)), c(COL_ND)), f_sum_n())),
        eq_g(g_block_n(), n(COL_ID), c(COL_ID)),
        eq_g(g_inner_n(), n(COL_SEEN), c(COL_SEEN)),
        eq_g(g_inner_n(), n(COL_P80), c(COL_P80)),
        eq_g(g_inner_n(), n(COL_LAST), c(COL_LAST)),
        eq_g(n(col_r(0)), n(COL_SEEN), mul(c(COL_D), add(c(COL_SEEN), c(COL_P80)))),
        sub(c(COL_PN), mul(c(COL_P80), not(c(COL_LAST)))),
        mul(c(COL_SEEN), c(COL_P80)),
    ]);
    v.extend([
        mul(mul(r(3), c(COL_P80)), c(col_f(15))),
        mul(mul(r(3), sub(not(c(COL_SEEN)), c(COL_P80))), not(c(col_f(15)))),
        mul(mul(r(0), c(COL_SEEN)), c(col_f(0))),
        mul(mul(r(0), c(COL_LAST)), sub(not(c(COL_SEEN)), c(COL_P80))),
        mul(mul(r(0), c(COL_SEEN)), not(c(COL_LAST))),
        mul(mul(r(3), c(COL_LAST)), c(col_f(8))),
        mul(mul(mul(r(3), c(COL_LAST)), c(COL_P80)), drop_e(8)),
        mul(mul(r(3), c(COL_PN)), not(c(col_f(7)))),
    ]);
    for j in 0..4 {
        for q in 0..16 {
            let gate = mul(r(j), not(c(col_f(q))));
            v.push(if 16 * j + q < 56 {
                mul(gate, sub(byte_e(q), smul(128, mul(c(COL_P80), drop_e(q)))))
            } else {
                mul(gate, sub(mul(not(c(COL_LAST)), byte_e(q)), smul(128, mul(c(COL_PN), drop_e(q)))))
            });
        }
    }
    let r3l = || mul(r(3), c(COL_LAST));
    v.extend((0..32).map(|b| mul(r3l(), c(col_w(2, b)))));
    v.extend((28..32).map(|b| mul(r3l(), c(col_w(3, b)))));
    v.push(mul(r3l(), sub(bits(&|b| c(col_w(3, b)), 0, 28), smul(8, c(COL_ND)))));
    v.push(mul(c(COL_DMULT), not(c(COL_D))));
    v.push(mul(c(COL_DMULT), not(c(COL_LAST))));
    v
}

/// `ZkFormal.Sha.Table.constraints` (user constraints, no bit constraints).
pub fn sha_constraints() -> Vec<Expr> {
    let mut v: Vec<Expr> = bool_cols().into_iter().map(bool_c).collect();
    v.extend(c_kind());
    v.extend(c_iv());
    for i in 0..4 {
        for l in 0..2 {
            v.push(round_a(i, l));
            v.push(round_e(i, l));
        }
    }
    for i in 0..4 {
        for l in 0..2 {
            v.push(sched(i, l));
        }
    }
    v.extend(c_help());
    v.extend(c_digest());
    v.extend(c_frame());
    v
}

fn pos_e(q: usize) -> Expr { add(sub(c(COL_ND), f_sum_c()), k(q as u64)) }
fn digest_byte_e(p: usize) -> Expr { bits(&|b| c(col_st(p / 4, b)), 8 * (3 - p % 4), 8) }

pub fn sha_interactions(bus_bytes: usize, bus_digest: usize) -> Vec<Interaction> {
    let mut v: Vec<Interaction> = (0..16)
        .map(|q| Interaction {
            bus: bus_bytes,
            mult: vec![c(col_f(q))],
            msg: vec![c(COL_ID), pos_e(q), byte_e(q)],
            send: false,
        })
        .collect();
    let mut msg = vec![c(COL_ID), c(COL_ND)];
    msg.extend((0..32).map(digest_byte_e));
    v.push(Interaction { bus: bus_digest, mult: vec![c(COL_DMULT)], msg, send: true });
    v
}

fn with_bits(mut t: Table) -> Table {
    let b = crate::aux::bit_constraints(&t);
    t.constraints.extend(b);
    t
}

/// `ZkFormal.Sha.Table.table busBytes busDigest` (with its bit constraints).
pub fn sha_table(bus_bytes: usize, bus_digest: usize) -> Table {
    with_bits(Table {
        name: "sha256".into(),
        width: WIDTH,
        constraints: sha_constraints(),
        interactions: sha_interactions(bus_bytes, bus_digest),
        max_log: 22,
    })
}

pub const BUS_BYTES: usize = 0;
pub const BUS_DIGEST: usize = 1;

pub fn bytes_table() -> Table {
    with_bits(Table {
        name: "bytes".into(),
        width: 4,
        constraints: vec![],
        interactions: vec![Interaction { bus: BUS_BYTES, mult: vec![c(3)], msg: vec![c(0), c(1), c(2)], send: true }],
        max_log: 22,
    })
}

pub fn digest_table() -> Table {
    with_bits(Table {
        name: "digest".into(),
        width: 35,
        constraints: vec![],
        interactions: vec![Interaction { bus: BUS_DIGEST, mult: vec![c(34)], msg: (0..34).map(c).collect(), send: false }],
        max_log: 22,
    })
}

/// `Conformance.Sha.shaAir`.
pub fn sha_air() -> Air {
    Air { tables: vec![sha_table(BUS_BYTES, BUS_DIGEST), bytes_table(), digest_table()], num_buses: 2, num_pub: 0 }
}

// ---------------------------------------------------------------------------
// Honest trace (ZkFormal.Sha.Gen)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Msg {
    pub id: u32,
    pub bytes: Vec<u8>,
    /// whether the digest is provided on the digest bus (`Gen.Msg.dmult : Bool`)
    pub dmult: bool,
}

/// `Conformance.Sha.toyMsgs`: message `i` has id `i+1`, dmult 1, byte `j` =
/// `(37 j + 11 i + 5) mod 256`.
pub fn toy_msgs(lens: &[usize]) -> Vec<Msg> {
    lens.iter()
        .enumerate()
        .map(|(i, &len)| Msg {
            id: i as u32 + 1,
            bytes: (0..len).map(|j| ((37 * j + 11 * i + 5) % 256) as u8).collect(),
            dmult: true,
        })
        .collect()
}

fn pad(m: &[u8]) -> Vec<u8> {
    let mut p = m.to_vec();
    p.push(0x80);
    while p.len() % 64 != 56 {
        p.push(0);
    }
    p.extend_from_slice(&((m.len() as u64) * 8).to_be_bytes());
    p
}

fn rotr(x: u32, r: u32) -> u32 { x.rotate_right(r) }
fn bsig0(x: u32) -> u32 { rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22) }
fn bsig1(x: u32) -> u32 { rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25) }
fn ssig0(x: u32) -> u32 { rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3) }
fn ssig1(x: u32) -> u32 { rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10) }
fn chf(x: u32, y: u32, z: u32) -> u32 { (x & y) ^ (!x & z) }
fn majf(x: u32, y: u32, z: u32) -> u32 { (x & y) ^ (x & z) ^ (y & z) }

fn lo16(x: u64) -> u64 { x % 65536 }
fn hi16(x: u64) -> u64 { x / 65536 }
fn limb_n(x: u64, l: usize) -> u64 { if l == 0 { lo16(x) } else { hi16(x) } }
fn carry(xs: &[u64], l: usize) -> u64 {
    let c0 = xs.iter().map(|&x| lo16(x)).sum::<u64>() / 65536;
    if l == 0 { c0 } else { (xs.iter().map(|&x| hi16(x)).sum::<u64>() + c0) / 65536 }
}

/// One block (`Gen.Blk`) with its precomputed `As`, `Es`, `W`.
struct Blk {
    id: u64,
    len: usize,
    idx: usize,
    nblk: usize,
    hin: [u32; 8],
    dmult: u64,
    a: [u32; 68],
    e: [u32; 68],
    w: [u32; 64],
}

impl Blk {
    fn new(id: u64, len: usize, idx: usize, nblk: usize, hin: [u32; 8], blk: &[u8], dmult: u64) -> Blk {
        let mut w = [0u32; 64];
        for t in 0..16 {
            w[t] = u32::from_be_bytes(blk[4 * t..4 * t + 4].try_into().unwrap());
        }
        for t in 16..64 {
            w[t] = ssig1(w[t - 2]).wrapping_add(w[t - 7]).wrapping_add(ssig0(w[t - 15])).wrapping_add(w[t - 16]);
        }
        let mut a = [0u32; 68];
        let mut e = [0u32; 68];
        a[..4].copy_from_slice(&[hin[3], hin[2], hin[1], hin[0]]);
        e[..4].copy_from_slice(&[hin[7], hin[6], hin[5], hin[4]]);
        for t in 0..64 {
            let t1 = e[t]
                .wrapping_add(bsig1(e[t + 3]))
                .wrapping_add(chf(e[t + 3], e[t + 2], e[t + 1]))
                .wrapping_add(K[t])
                .wrapping_add(w[t]);
            let t2 = bsig0(a[t + 3]).wrapping_add(majf(a[t + 3], a[t + 2], a[t + 1]));
            a[t + 4] = t1.wrapping_add(t2);
            e[t + 4] = a[t].wrapping_add(t1);
        }
        Blk { id, len, idx, nblk, hin, dmult, a, e, w }
    }
    fn is_data(&self, kk: usize) -> bool { 64 * self.idx + kk < self.len }
    fn last(&self) -> bool { self.idx + 1 == self.nblk }
    fn p80(&self) -> bool { 64 * self.idx <= self.len && self.len < 64 * self.idx + 64 }
    fn seen(&self) -> bool { self.len < 64 * self.idx }
    fn terms_a(&self, t: usize) -> [u64; 7] {
        let (a, e) = (&self.a, &self.e);
        [e[t], bsig1(e[t + 3]), chf(e[t + 3], e[t + 2], e[t + 1]), K[t], self.w[t], bsig0(a[t + 3]),
            majf(a[t + 3], a[t + 2], a[t + 1])]
        .map(|x| x as u64)
    }
    fn terms_e(&self, t: usize) -> [u64; 6] {
        let (a, e) = (&self.a, &self.e);
        [a[t], e[t], bsig1(e[t + 3]), chf(e[t + 3], e[t + 2], e[t + 1]), K[t], self.w[t]].map(|x| x as u64)
    }
    fn help(&self, m: usize, l: usize) -> u64 {
        limb_n(ssig0(self.w[m + 1]) as u64, l) + limb_n(self.w[m] as u64, l)
    }
    fn sched_carry(&self, t: usize, l: usize) -> u64 {
        let s1 = ssig1(self.w[t - 2]) as u64;
        let w7 = self.w[t - 7] as u64;
        let c0 = (lo16(s1) + lo16(w7) + self.help(t - 16, 0)) / 65536;
        if l == 0 { c0 } else { (hi16(s1) + hi16(w7) + self.help(t - 16, 1) + c0) / 65536 }
    }
    fn fin(&self, w: usize) -> u32 { if w < 4 { self.a[67 - w] } else { self.e[71 - w] } }
    fn hout(&self, w: usize) -> u32 { self.hin[w].wrapping_add(self.fin(w)) }
    fn nd_row(&self, j: usize) -> u64 { self.len.min(64 * self.idx + 16 * (j.min(3) + 1)) as u64 }
    fn framing(&self, row: &mut [u64]) {
        row[COL_ID] = self.id;
        row[COL_LAST] = self.last() as u64;
        row[COL_P80] = self.p80() as u64;
        row[COL_SEEN] = self.seen() as u64;
        row[COL_PN] = (self.p80() && !self.last()) as u64;
    }

    /// `Gen.roundCell j B` for every column.
    fn round_row(&self, j: usize, row: &mut [u64]) {
        let t0 = 4 * j;
        let bit = |x: u64, b: usize| (x >> b) & 1;
        for i in 0..4 {
            for b in 0..32 {
                row[col_a(i, b)] = bit(self.a[t0 + 4 + i] as u64, b);
                row[col_e(i, b)] = bit(self.e[t0 + 4 + i] as u64, b);
                row[col_w(i, b)] = bit(self.w[t0 + i] as u64, b);
            }
            for l in 0..2 {
                let ca = carry(&self.terms_a(t0 + i), l);
                let ce = carry(&self.terms_e(t0 + i), l);
                let cw = if j >= 4 { self.sched_carry(t0 + i, l) } else { 0 };
                for kk in 0..3 {
                    row[col_ca(i, l, kk)] = bit(ca, kk);
                    row[col_ce(i, l, kk)] = bit(ce, kk);
                    row[col_cw(i, l, kk)] = bit(cw, kk);
                }
                // I4 / I8 / I12 (d = 1, 2, 3)
                for (d, col) in [(1, col_i4(i, l)), (2, col_i8(i, l)), (3, col_i12(i, l))] {
                    row[col] = if d <= j { self.help(4 * (j - d) + i, l) } else { 0 };
                }
                if i < 3 {
                    row[col_w3(i, l)] = if j >= 1 { limb_n(self.w[4 * (j - 1) + i + 1] as u64, l) } else { 0 };
                }
            }
        }
        for w in 0..8 {
            for l in 0..2 {
                row[col_hin(w, l)] = limb_n(self.hin[w] as u64, l);
            }
        }
        row[col_r(j)] = 1;
        for q in 0..16 {
            row[col_f(q)] = (j < 4 && self.is_data(16 * j + q)) as u64;
        }
        row[COL_FPREV] = if j == 0 { 1 } else { (j < 4 && self.is_data(16 * j - 1)) as u64 };
        row[COL_ND] = self.nd_row(j);
        self.framing(row);
    }

    /// `Gen.digestCell B` for every column.
    fn digest_row(&self, row: &mut [u64]) {
        for w in 0..8 {
            let h = self.hout(w) as u64;
            for b in 0..32 {
                row[col_st(w, b)] = (h >> b) & 1;
            }
            for l in 0..2 {
                let cv = carry(&[self.hin[w] as u64, self.fin(w) as u64], l);
                for kk in 0..3 {
                    row[col_cst(w, l, kk)] = (cv >> kk) & 1;
                }
            }
        }
        row[COL_D] = 1;
        row[COL_ND] = self.nd_row(4);
        self.framing(row);
        row[COL_DMULT] = if self.last() { self.dmult } else { 0 };
    }
}

/// `Gen.startCell id`.
fn start_row(id: u64, row: &mut [u64]) {
    for w in 0..8 {
        for b in 0..32 {
            row[col_st(w, b)] = ((H0[w] >> b) & 1) as u64;
        }
    }
    row[COL_S] = 1;
    row[COL_ID] = id;
}

enum RowDesc {
    Start(u64),
    Round(usize, usize),
    Digest(usize),
}

/// The SHA table rows (as `u64` cells, row-major, 2^log rows) plus the
/// number of non-padding rows and `log` (`Gen.honestLog`).
pub fn sha_cells(msgs: &[Msg]) -> (Vec<u64>, usize, usize) {
    // blocks, in message order
    let mut blks: Vec<Blk> = vec![];
    let mut rows: Vec<RowDesc> = vec![];
    for m in msgs {
        let p = pad(&m.bytes);
        let nblk = p.len() / 64;
        rows.push(RowDesc::Start(m.id as u64));
        let mut h = H0;
        for b in 0..nblk {
            let blk = Blk::new(m.id as u64, m.bytes.len(), b, nblk, h, &p[64 * b..64 * b + 64], m.dmult as u64);
            for (w, hw) in h.iter_mut().enumerate() {
                *hw = blk.hout(w);
            }
            for j in 0..16 {
                rows.push(RowDesc::Round(j, blks.len()));
            }
            rows.push(RowDesc::Digest(blks.len()));
            blks.push(blk);
        }
    }
    let nrows = rows.len();
    let log = (nrows.next_power_of_two().trailing_zeros() as usize).max(1);
    let mut cells = vec![0u64; WIDTH << log];
    cells.par_chunks_mut(WIDTH).zip(rows.par_iter()).for_each(|(row, d)| match *d {
        RowDesc::Start(id) => start_row(id, row),
        RowDesc::Round(j, b) => blks[b].round_row(j, row),
        RowDesc::Digest(b) => blks[b].digest_row(row),
    });
    (cells, nrows, log)
}

fn to_matrix(cells: &[u64], width: usize) -> RowMajorMatrix<F> {
    RowMajorMatrix::new(cells.par_iter().map(|&x| F::new(x as u32)).collect(), width)
}

fn pow2_rows(n: usize) -> usize { n.next_power_of_two().max(2) }

/// Honest traces for `sha_air()`: SHA table, byte provider, digest consumer.
pub fn sha_traces(msgs: &[Msg]) -> Vec<RowMajorMatrix<F>> {
    let (cells, _, _) = sha_cells(msgs);
    let nb: usize = msgs.iter().map(|m| m.bytes.len()).sum();
    let mut bytes = vec![F::new(0); 4 * pow2_rows(nb)];
    let mut r = 0;
    for m in msgs {
        for (p, &x) in m.bytes.iter().enumerate() {
            bytes[4 * r..4 * r + 4].copy_from_slice(&[F::new(m.id), F::new(p as u32), F::new(x as u32), F::new(1)]);
            r += 1;
        }
    }
    let mut dig = vec![F::new(0); 35 * pow2_rows(msgs.len())];
    for (r, m) in msgs.iter().enumerate() {
        let d = Sha256::digest(&m.bytes);
        let row = &mut dig[35 * r..35 * r + 35];
        row[0] = F::new(m.id);
        row[1] = F::new(m.bytes.len() as u32);
        for (p, &x) in d.iter().enumerate() {
            row[2 + p] = F::new(x as u32);
        }
        row[34] = F::new(m.dmult as u32);
    }
    vec![to_matrix(&cells, WIDTH), RowMajorMatrix::new(bytes, 4), RowMajorMatrix::new(dig, 35)]
}

/// Dump in the `np-lean-shatrace` format: LE u32 `width, log, nrows`, then
/// all `2^log · width` cells row-major.
pub fn dump_trace(msgs: &[Msg]) -> Vec<u8> {
    let (cells, nrows, log) = sha_cells(msgs);
    let mut out = Vec::with_capacity(4 * (3 + cells.len()));
    for x in [WIDTH as u32, log as u32, nrows as u32] {
        out.extend_from_slice(&x.to_le_bytes());
    }
    for x in cells {
        out.extend_from_slice(&(x as u32).to_le_bytes());
    }
    out
}
