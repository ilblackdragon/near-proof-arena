//! Trace generation for the SHA-512 compression AIR v4.
use crate::s384::air::*;
use crate::s384::air::Kind::*;
pub use crate::s384::reference::*;

pub const P: u64 = 2013265921;

/// a_t, e_t (t >= -4) and W_t of a compression's words.
pub fn ga(wd: &Words, t: i64) -> u64 {
    wd.a[(t + 4) as usize]
}
pub fn ge(wd: &Words, t: i64) -> u64 {
    wd.e[(t + 4) as usize]
}
pub fn gw(wd: &Words, t: i64) -> u64 {
    wd.w[t as usize]
}

pub struct Traces {
    pub main: Vec<u32>,
    pub main_height: usize,
    pub table: Vec<u32>,
    pub harness: Vec<u32>,
    pub harness_height: usize,
}

pub fn main_height(n: usize) -> usize {
    (n * ROWS).next_power_of_two().max(4)
}

type L3 = [i64; 3];
fn l3(x: u64) -> L3 {
    limbs(x).map(|v| v as i64)
}
fn sum3(xs: &[L3]) -> L3 {
    std::array::from_fn(|i| xs.iter().map(|x| x[i]).sum())
}
fn neg3(x: L3) -> L3 {
    x.map(|v| -v)
}
pub fn fe(v: i64) -> u32 {
    v.rem_euclid(P as i64) as u32
}

/// Carries for out_i + 2^{w_i} c_i - c_{i-1} = rhs_i, stored with offset `off`.
pub fn carries(out: u64, rhs: L3, off: i64) -> L3 {
    let ol = l3(out);
    let mut c = [0i64; 3];
    let mut prev = 0i64;
    for i in 0..3 {
        let w = lw(i) as i64;
        let v = rhs[i] + prev - ol[i];
        assert_eq!(v.rem_euclid(1 << w), 0, "limb mismatch");
        c[i] = v >> w;
        prev = c[i];
        assert!((0..CARRY_RANGE as i64).contains(&(c[i] + off)), "carry {} off {off}", c[i]);
    }
    c.map(|x| x + off)
}

/// Main trace (row-major).  `height` >= n*ROWS, a power of two; padding rows are all zero.
pub fn gen_main(comps: &[Comp], height: usize) -> Vec<u32> {
    assert!(height >= comps.len() * ROWS && height.is_power_of_two());
    let mut t = vec![0u32; height * WIDTH];
    for (s, c) in comps.iter().enumerate() {
        let wd = round_words(c);
        for r in 0..ROWS {
            let gi = s * ROWS + r;
            let row = &mut t[gi * WIDTH..(gi + 1) * WIDTH];
            fill_row(row, &wd, r, gi);
        }
    }
    t
}

/// The two slot words of segment row r.
pub fn slot_words(wd: &Words, r: usize) -> (u64, u64) {
    let k = kind_of(r);
    if k.is_a() {
        let j = (r - AB) as i64;
        (ga(wd, 2 * j - 4), ga(wd, 2 * j - 3))
    } else if k.is_e() {
        let j = (r - EB) as i64;
        (ge(wd, 2 * j - 4), ge(wd, 2 * j - 3))
    } else if k.is_w() {
        let j = r - WB;
        (wd.w[2 * j + 1], wd.w[2 * j])
    } else {
        let kk = r - OB;
        (wd.out[2 * kk + 1], wd.out[2 * kk])
    }
}

fn fill_row(row: &mut [u32], wd: &Words, r: usize, gi: usize) {
    let kind = kind_of(r);
    let (k1, k2) = kind.code();
    row[C_R] = r as u32;
    row[C_G] = gi as u32;
    row[C_K1] = k1 as u32;
    row[C_K2] = k2 as u32;
    let (s0, s1) = slot_words(wd, r);
    for (j, d) in digits(s0).into_iter().enumerate() {
        row[D0 + j] = d as u32;
    }
    for (j, d) in digits(s1).into_iter().enumerate() {
        row[D1 + j] = d as u32;
    }
    let mut put = |i: usize, v: L3| {
        for q in 0..3 {
            row[XA + i + q] = fe(v[q]);
        }
    };
    let ro = roles(kind);
    if kind.is_a() {
        let j = (r - AB) as i64;
        let a = |t: i64| ga(wd, t);
        if ro.r_a {
            // out-round t = 2j - 2, in-round t = 2j - 1; outputs on row j + 1
            let y = sum3(&[l3(bsig0(a(2 * j - 3))), l3(majf(a(2 * j - 3), a(2 * j - 4), a(2 * j - 5))), neg3(l3(a(2 * j - 6)))]);
            let d_in = l3(a(2 * j - 5));
            let co = carries(a(2 * j - 2), sum3(&[y, l3(ge(wd, 2 * j - 2))]), OFF_A);
            let m_in = sum3(&[l3(bsig0(a(2 * j - 2))), l3(majf(a(2 * j - 2), a(2 * j - 3), a(2 * j - 4)))]);
            let ci = carries(a(2 * j - 1), sum3(&[m_in, neg3(d_in), l3(ge(wd, 2 * j - 1))]), OFF_A);
            put(0, y);
            put(3, d_in);
            put(6, co);
            put(9, ci);
        }
        if ro.r2.is_some() {
            put(12, l3(gw(wd, 2 * j)));
        }
        if kind == A0 {
            // feed-forward of O_1: (H3 + a76, H2 + a77) = (H'3, H'2)
            put(0, l3(a(76)));
            put(3, l3(a(77)));
            put(6, carries(wd.out[3], sum3(&[l3(a(-4)), l3(a(76))]), 0));
            put(9, carries(wd.out[2], sum3(&[l3(a(-3)), l3(a(77))]), 0));
        }
        if kind == A41 {
            // feed-forward of O_0: (a78 + H1, a79 + H0) = (H'1, H'0)
            put(0, l3(a(-2)));
            put(3, l3(a(-1)));
            put(6, carries(wd.out[1], sum3(&[l3(a(78)), l3(a(-2))]), 0));
            put(9, carries(wd.out[0], sum3(&[l3(a(79)), l3(a(-1))]), 0));
        }
    } else if kind.is_e() {
        let j = (r - EB) as i64;
        let e = |t: i64| ge(wd, t);
        if ro.r_e {
            let hpp = sum3(&[l3(e(2 * j - 6)), l3(K[(2 * j - 2) as usize])]);
            let hp = sum3(&[l3(e(2 * j - 5)), l3(K[(2 * j - 1) as usize])]);
            let l_out = sum3(&[l3(bsig1(e(2 * j - 3))), l3(chf(e(2 * j - 3), e(2 * j - 4), e(2 * j - 5)))]);
            let l_in = sum3(&[l3(bsig1(e(2 * j - 2))), l3(chf(e(2 * j - 2), e(2 * j - 3), e(2 * j - 4)))]);
            let dw0 = sum3(&[l3(ga(wd, 2 * j - 6)), l3(gw(wd, 2 * j - 2))]);
            let dw1 = sum3(&[l3(gw(wd, 2 * j - 1)), l3(ga(wd, 2 * j - 5))]);
            put(0, hpp);
            put(3, hp);
            put(6, carries(e(2 * j - 2), sum3(&[hpp, l_out, dw0]), 0));
            put(9, carries(e(2 * j - 1), sum3(&[hp, l_in, dw1]), 0));
            put(12, l_out);
        }
        if kind == E0 {
            // feed-forward of O_3: (H7 + e76, H6 + e77) = (H'7, H'6)
            put(0, l3(e(76)));
            put(3, l3(e(77)));
            put(6, carries(wd.out[7], sum3(&[l3(e(-4)), l3(e(76))]), 0));
            put(9, carries(wd.out[6], sum3(&[l3(e(-3)), l3(e(77))]), 0));
        }
        if kind == E41 {
            // feed-forward of O_2: (e78 + H5, e79 + H4) = (H'5, H'4)
            put(0, l3(e(-2)));
            put(3, l3(e(-1)));
            put(6, carries(wd.out[5], sum3(&[l3(e(78)), l3(e(-2))]), 0));
            put(9, carries(wd.out[4], sum3(&[l3(e(79)), l3(e(-1))]), 0));
        }
    } else if kind.is_w() {
        let j = (r - WB) as i64;
        let w = |t: i64| gw(wd, t);
        put(12, l3(ga(wd, 2 * j - 3)));
        if ro.r_w {
            let v0 = sum3(&[l3(w(2 * j - 14)), l3(ssig0(w(2 * j - 13)))]);
            let v1 = sum3(&[l3(w(2 * j - 13)), l3(ssig0(w(2 * j - 12)))]);
            put(0, v0);
            put(3, v1);
            put(6, carries(w(2 * j + 2), sum3(&[l3(ssig1(w(2 * j))), v0, l3(w(2 * j - 5))]), 0));
            put(9, carries(w(2 * j + 3), sum3(&[l3(ssig1(w(2 * j + 1))), v1, l3(w(2 * j - 4))]), 0));
        }
    }
}

/// Table trace (128 rows): index bits and multiplicities counted from the main trace.
pub fn gen_table(main: &[u32], height: usize) -> Vec<u32> {
    let mut t = vec![0u32; ROWS * T_WIDTH];
    for i in 0..ROWS {
        for bit in 0..T_BITS {
            t[i * T_WIDTH + bit] = ((i >> bit) & 1) as u32;
        }
    }
    for gi in 0..height {
        let row = &main[gi * WIDTH..(gi + 1) * WIDTH];
        if row[C_K1] == 0 {
            continue;
        }
        let r = row[C_R] as usize;
        t[r * T_WIDTH + T_MC] += 1;
        if roles(kind_of(r)).k_lookup {
            t[r * T_WIDTH + T_MK] += 1;
        }
    }
    t
}

/// Interface consumer rows from the reference compression (independent of the AIR trace).
pub fn gen_harness(comps: &[Comp]) -> (Vec<u32>, usize) {
    let height = (comps.len() * 16).next_power_of_two().max(4);
    let mut t = vec![0u32; height * H_WIDTH];
    for (s, c) in comps.iter().enumerate() {
        let out = sha2_compress(c);
        let ws: Vec<u64> = c.h.iter().chain(c.block.iter()).chain(out.iter()).copied().collect();
        for m in 0..16 {
            let row = &mut t[(s * 16 + m) * H_WIDTH..][..H_WIDTH];
            row[0] = (s * ROWS) as u32;
            row[1] = m as u32;
            for (h, wv) in [ws[2 * m], ws[2 * m + 1]].into_iter().enumerate() {
                for (i, v) in limbs(wv).into_iter().enumerate() {
                    row[2 + 3 * h + i] = v as u32;
                }
            }
            row[8] = 1;
        }
    }
    (t, height)
}

pub fn gen_all(comps: &[Comp]) -> Traces {
    let h = main_height(comps.len());
    let main = gen_main(comps, h);
    let table = gen_table(&main, h);
    let (harness, hh) = gen_harness(comps);
    Traces { main, main_height: h, table, harness, harness_height: hh }
}

/// Word in slot `slot` of trace row gi.
pub fn get_word(main: &[u32], gi: usize, slot: usize) -> u64 {
    let base = gi * WIDTH + if slot == 0 { D0 } else { D1 };
    (0..ND).fold(0u64, |acc, j| acc | ((main[base + j] as u64) << (2 * j)))
}

/// Output state read back from the O rows of compression s.
pub fn trace_output(main: &[u32], s: usize) -> [u64; 8] {
    std::array::from_fn(|i| get_word(main, s * ROWS + OB + i / 2, if i % 2 == 0 { 1 } else { 0 }))
}

