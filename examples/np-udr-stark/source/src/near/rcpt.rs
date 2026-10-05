//! Honest rows of the `rcpt` table — a cell-for-cell port of
//! `zk-formal/ZkFormal/Near/Render/Rcpt.lean` (`RcptGen.*`, `rdOf`,
//! `rcptData`, `rcptRowsAll`) and `rcptMsgs` of `Render/RcptSim.lean`.
//!
//! Column layout: `Tables/Rcpt/Layout.lean`; the emission slots are filled by
//! evaluating the table's `emits` (`Tables/Rcpt/Fields.lean`), transcribed in
//! [`emits`] below.  Cells are computed as naturals (`u64`, all small) and
//! reduced mod `p` on output, exactly like `Fp.ofNat` on the Lean rows.

use super::ext::{burnt_of, surplus_of};
use super::info::{sha_n, tprev_of, Info, Msg};
use super::sim::{has_refund, peo_bytes, rcpt_msgs_sim, rid_bytes};
use super::spec::gas_refund_receipt;

// ---------------------------------------------------------------------------
// Layout (`Tables/Rcpt/Layout.lean`)
// ---------------------------------------------------------------------------

#[allow(dead_code)]
pub mod col {
    pub const ACT: usize = 0;
    pub const RF: usize = 1;
    pub const RL: usize = 2;
    pub const LAST_R: usize = 3;
    pub const S_CL: usize = 4;
    pub const S_PL: usize = 5;
    pub const S_P: usize = 6;
    pub const S_VL: usize = 7;
    pub const S_V: usize = 8;
    pub const S_RID: usize = 9;
    pub const S_T0: usize = 10;
    pub const S_SL: usize = 11;
    pub const S_S: usize = 12;
    pub const S_KT: usize = 13;
    pub const S_PK: usize = 14;
    pub const S_GP: usize = 15;
    pub const S_TL: usize = 16;
    pub const S_DEP: usize = 17;
    pub const S_XP0: usize = 18;
    pub const S_XRI: usize = 19;
    pub const S_XG: usize = 20;
    pub const S_XST: usize = 21;
    pub const S_XL0: usize = 22;
    pub const S_XLH: usize = 23;
    pub const S_XRH: usize = 24;
    pub const S_XRF: usize = 25;
    pub const S_XRZ: usize = 26;
    pub const IDX: usize = 27;
    pub const FS: usize = 28;
    pub const FE: usize = 29;
    pub const B: usize = 30;
    pub const T_A: usize = 43;
    pub const SYM_A: usize = 44;
    pub const LAST_A: usize = 45;
    pub const G_KA: usize = 46;
    pub const KZ: usize = 47;
    pub const R: usize = 48;
    pub const O: usize = 49;
    pub const O2: usize = 50;
    pub const LP: usize = 51;
    pub const LV: usize = 52;
    pub const LS: usize = 53;
    pub const KT: usize = 54;
    pub const HR: usize = 55;
    pub const KSLOT: usize = 56;
    pub const TPREV: usize = 57;
    pub const RCNT: usize = 58;
    pub const GE: usize = 59;
    pub const BIG: usize = 60;
    pub const O_END: usize = 61;
    pub const O2_END: usize = 62;
    pub const fn reg(i: usize) -> usize {
        63 + i
    }
    pub const fn tok(i: usize) -> usize {
        95 + i
    }
    pub const H2: usize = 111;
    pub const H3: usize = 112;
    pub const H5: usize = 113;
    pub const H6: usize = 114;
    pub const H7: usize = 115;
    pub const fn lb(i: usize) -> usize {
        116 + i
    }
    pub const Z: usize = 120;
    pub const LINV: usize = 121;
    pub const L210: usize = 122;
    pub const HX6: usize = 123;
    pub const ACC: usize = 124;
    pub const VC0: usize = 125;
    pub const VC1: usize = 126;
    pub const H01: usize = 127;
    pub const P1: usize = 128;
    pub const P2: usize = 129;
    pub const P3: usize = 130;
    pub const I1: usize = 131;
    pub const I2: usize = 132;
    pub const I3: usize = 133;
    pub const ISYS: usize = 134;
    pub const R1: usize = 135;
    pub const LO8: usize = 136;
    pub const LO4: usize = 137;
    pub const fn xb(i: usize) -> usize {
        138 + i
    }
    pub const C1: usize = 204;
    pub const C2: usize = 205;
    pub const C3: usize = 206;
    pub const C4: usize = 207;
    pub const fn dl(i: usize) -> usize {
        208 + i
    }
    pub const BURNT: usize = 216;
    pub const RAMT: usize = 217;
    pub const SUM_D: usize = 218;
    pub const INV_A: usize = 219;
    pub const BEF: usize = 220;
    pub const LK: usize = 221;
    pub const ST: usize = 222;
    pub const DSUM: usize = 223;
    pub const INV_B: usize = 224;
    pub const D_I: usize = 225;
    pub const D_L: usize = 226;
    pub const G_DG: usize = 227;
    pub const WIDTH: usize = 228;
    pub const fn e_id(e: usize) -> usize {
        31 + 4 * e
    }
    pub const fn e_pos(e: usize) -> usize {
        32 + 4 * e
    }
    pub const fn e_v(e: usize) -> usize {
        33 + 4 * e
    }
    pub const fn e_g(e: usize) -> usize {
        34 + 4 * e
    }
}

use col::*;

// ---------------------------------------------------------------------------
// Constants (`Ids.lean`, `Tables/Rcpt/Arith.lean`, `NearSpec.Params`)
// ---------------------------------------------------------------------------

/// The field modulus (BabyBear).
const PM: u64 = 2013265921;

const K_RC: u64 = 1;
const K_RF: u64 = 2;
const K_PEO: u64 = 3;
const K_LEAF: u64 = 4;
const K_RID: u64 = 5;
const SYM_END: u64 = 16;

const PV_SHARD: usize = 77;
const PV_HEIGHT: usize = 85;
const PV_BGP: usize = 93;
const PV_GASLIM: usize = 109;
const PV_N: usize = 149;
const PV_NREF: usize = 249;
const PV_GAS: usize = 285;

const G_LE: [u64; 8] = [196, 164, 183, 246, 51, 0, 0, 0];
const S_LE: [u64; 8] = [0, 0, 232, 137, 4, 35, 199, 138];
/// `Params.G`
const GAS_G: u128 = 223182562500;
/// `Params.storageAmountPerByte`
const STORAGE_PER_BYTE: u128 = 10_000_000_000_000_000_000;

/// `regStates` (`Tables/Rcpt/Arith.lean`): states whose byte is the register head.
const REG_STATES: [usize; 15] = [
    S_PL, S_VL, S_SL, S_T0, S_KT, S_TL, S_XP0, S_XG, S_XST, S_XL0, S_XRH, S_XRF, S_XRZ, S_XRI, S_XLH,
];

fn msg_id(kind: u64, idx: u64) -> u64 {
    kind + 16 * idx
}

// ---------------------------------------------------------------------------
// Small helpers (`RcptGen`)
// ---------------------------------------------------------------------------

type Row = Vec<u64>;

fn zero_row() -> Row {
    vec![0; WIDTH]
}

fn b2n(x: bool) -> u64 {
    x as u64
}

fn bit_of(x: u64, j: usize) -> u64 {
    if j >= 64 { 0 } else { (x >> j) & 1 }
}

/// `x^(p−2) mod p` (`0 ↦ 0`); `x` is reduced first.
fn inv_p(x: u64) -> u64 {
    let mut b = x % PM;
    let mut e = PM - 2;
    let mut acc = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            acc = acc * b % PM;
        }
        b = b * b % PM;
        e >>= 1;
    }
    if x % PM == 0 { 0 } else { acc }
}

/// `leBytes w x` for `x < 2^128` (bytes beyond 16 are 0).
fn le_bytes(w: usize, x: u128) -> Vec<u64> {
    (0..w).map(|i| if i < 16 { ((x >> (8 * i)) & 255) as u64 } else { 0 }).collect()
}

fn get(l: &[u64], i: usize) -> u64 {
    l.get(i).copied().unwrap_or(0)
}

/// `setBits row off len x`
fn set_bits(rw: &mut Row, off: usize, len: usize, x: u64) {
    for j in 0..len {
        rw[xb(off + j)] = bit_of(x, j);
    }
}

/// `conv g v i = Σ_{j ≤ i} g_j · v_{i−j}`
fn conv(g: &[u64], v: &[u64], i: usize) -> u64 {
    (0..g.len()).filter(|&j| j <= i).map(|j| g[j] * get(v, i - j)).sum()
}

/// Character columns of an account-id byte (`setChar`).
fn set_char(rw: &mut Row, ch: u64) {
    let hi = ch / 16;
    let lo = ch % 16;
    for (c, v) in [(H2, 2), (H3, 3), (H5, 5), (H6, 6), (H7, 7)] {
        rw[c] = b2n(hi == v);
    }
    for j in 0..4 {
        rw[lb(j)] = bit_of(lo, j);
    }
    rw[Z] = b2n(lo == 0);
    rw[LINV] = if lo == 0 { 0 } else { inv_p(lo) };
    rw[L210] = b2n(lo % 8 == 7);
    rw[HX6] = b2n(hi == 6 && 1 <= lo && lo <= 6);
}

fn is_hex_c(ch: u64) -> bool {
    (48..=57).contains(&ch) || (97..=102).contains(&ch)
}

/// `(x : Int)^2` as a natural (`x` small).
fn sq(x: i128) -> u64 {
    (x * x) as u64
}

/// Per-receipt data (`RcptGen.RD`).  Amounts are kept modulo `2^128`
/// (`leBytes 16` truncates the same way); comparisons are exact.
#[derive(Clone, Debug, Default)]
pub struct Rd {
    pub r: u64,
    pub pred: Vec<u64>,
    pub recv: Vec<u64>,
    pub id: Vec<u64>,
    pub signer: Vec<u64>,
    pub kt: u64,
    pub pk: Vec<u64>,
    pub gp: u128,
    pub dep: u128,
    pub hr: bool,
    pub ge: bool,
    pub kslot: u64,
    pub tprev: u64,
    pub bef: u128,
    pub locked: u128,
    pub stor: u128,
    pub big: bool,
    pub burnt: u128,
    pub ramt: u128,
    pub tok0: u128,
    pub o: u64,
    pub o2: u64,
    pub rcnt: u64,
    pub refund_id: Vec<u64>,
    pub peo_len: u64,
    pub peo_dig: Vec<u64>,
}

/// Field plan `(state, length, register load)` (`RcptGen.plan`).
fn plan(d: &Rd, pubv: &[u64]) -> Vec<(usize, usize, Vec<u64>)> {
    let pubs = |off: usize, len: usize| -> Vec<u64> { (0..len).map(|j| get(pubv, off + j)).collect() };
    let lp = d.pred.len();
    let lv = d.recv.len();
    let ls = d.signer.len();
    let mut pl = vec![
        (S_PL, 4, vec![lp as u64, 0, 0, 0]),
        (S_P, lp, vec![115, 121, 115, 116, 101, 109]),
        (S_VL, 4, vec![lv as u64, 0, 0, 0]),
        (S_V, lv, vec![]),
        (S_RID, 32, vec![]),
        (S_T0, 1, vec![0]),
        (S_SL, 4, vec![ls as u64, 0, 0, 0]),
        (S_S, ls, vec![]),
        (S_KT, 1, vec![d.kt]),
        (S_PK, (32 + 32 * d.kt) as usize, vec![]),
        (S_GP, 16, pubs(PV_BGP, 16)),
        (S_TL, 13, vec![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3]),
        (S_DEP, 16, vec![]),
        (S_XP0, 4, vec![b2n(d.hr), 0, 0, 0]),
    ];
    if d.hr {
        pl.push((S_XRI, 32, d.refund_id.clone()));
    }
    pl.push((S_XG, 8, G_LE.to_vec()));
    pl.push((S_XST, 5, vec![2, 0, 0, 0, 0]));
    pl.push((S_XL0, 4, vec![2, 0, 0, 0]));
    pl.push((S_XLH, 32, d.peo_dig.clone()));
    if d.hr {
        let mut h = pubs(PV_HEIGHT, 8);
        h.extend([0; 8]);
        pl.push((S_XRH, 16, h));
        pl.push((S_XRF, 10, vec![6, 0, 0, 0, 115, 121, 115, 116, 101, 109]));
        pl.push((S_XRZ, 16, vec![0; 16]));
    }
    pl
}

/// Rows of one receipt segment (`RcptGen.segRows`).
fn seg_rows(d: &Rd, pubv: &[u64], bgp_b: &[u64]) -> Vec<Row> {
    let pl = plan(d, pubv);
    let gp_b = le_bytes(16, d.gp);
    let dep_b = le_bytes(16, d.dep);
    let bef_b = le_bytes(16, d.bef);
    let lk_b = le_bytes(16, d.locked);
    let st_b = le_bytes(8, d.stor);
    let aft = d.bef.wrapping_add(d.dep);
    let aft_b = le_bytes(16, aft);
    let tot_b = le_bytes(16, aft.wrapping_add(d.locked));
    let q_b = le_bytes(16, STORAGE_PER_BYTE.wrapping_mul(d.stor));
    let p_b: Vec<u64> = (0..16).map(|i| if d.ge { get(bgp_b, i) } else { get(&gp_b, i) }).collect();
    // gas: gp − bgp with borrow: (borrow-in, D, borrow-out)
    let mut gp_diff: Vec<(u64, u64, u64)> = Vec::with_capacity(16);
    {
        let mut br: i64 = 0;
        for i in 0..16 {
            let t = get(&gp_b, i) as i64 - get(bgp_b, i) as i64 - br;
            let (dv, bo) = if t < 0 { ((t + 256) as u64, 1) } else { (t as u64, 0) };
            gp_diff.push((br as u64, dv, bo));
            br = bo as i64;
        }
    }
    let sur_b: Vec<u64> = gp_diff.iter().map(|&(_, dv, _)| if d.ge { dv } else { 0 }).collect();
    let tok_old = le_bytes(16, d.tok0);
    let tok_new = le_bytes(16, d.tok0.wrapping_add(d.burnt));
    let (lp, lv, ls) = (d.pred.len() as u64, d.recv.len() as u64, d.signer.len() as u64);
    let o_end = d.o + 123 + lp + lv + ls + 32 * d.kt;
    let o2_end = d.o2 + if d.hr { 129 + 2 * ls + 32 * d.kt } else { 0 };
    let mut base = zero_row();
    base[ACT] = 1;
    for (c, v) in [
        (R, d.r),
        (O, d.o),
        (O2, d.o2),
        (LP, lp),
        (LV, lv),
        (LS, ls),
        (KT, d.kt),
        (HR, b2n(d.hr)),
        (KSLOT, d.kslot),
        (TPREV, d.tprev),
        (RCNT, d.rcnt),
        (GE, b2n(d.ge)),
        (BIG, b2n(d.big)),
        (O_END, o_end),
        (O2_END, o2_end),
    ] {
        base[c] = v;
    }
    let g5 = &G_LE[..5];
    let mut rows: Vec<Row> = Vec::new();
    let nf = pl.len();
    for (fi, (s, len, ld)) in pl.iter().enumerate() {
        let (s, len) = (*s, *len);
        let mut cc1: u64 = 0;
        let mut cc2: u64 = 0;
        let mut cc3: u64 = 0;
        let mut cc4: u64 = 0;
        let mut run_d: u64 = 0;
        let mut run_a: u64 = 0;
        let mut acc_v: u64 = 0;
        let strv: &[u64] = if s == S_P {
            &d.pred
        } else if s == S_V {
            &d.recv
        } else {
            &d.signer
        };
        for i in 0..len {
            let mut rw = base.clone();
            rw[s] = 1;
            rw[IDX] = i as u64;
            rw[FS] = b2n(i == 0);
            rw[FE] = b2n(i + 1 == len);
            rw[RL] = b2n(i + 1 == len && fi + 1 == nf);
            rw[RF] = b2n(s == S_PL && i == 0);
            for j in 0..32 {
                rw[reg(j)] = get(ld, i + j);
            }
            // tokens register: old bytes before GP, rotated in GP, new bytes after
            let before_gp = matches!(s, S_PL | S_P | S_VL | S_V | S_RID | S_T0 | S_SL | S_S | S_KT | S_PK);
            for j in 0..16 {
                rw[tok(j)] = if before_gp {
                    get(&tok_old, j)
                } else if s == S_GP {
                    if i + j < 16 { get(&tok_old, i + j) } else { get(&tok_new, i + j - 16) }
                } else {
                    get(&tok_new, j)
                };
            }
            // the row's byte
            let bv: u64 = if REG_STATES.contains(&s) {
                get(ld, i)
            } else if s == S_P || s == S_V || s == S_S {
                get(strv, i)
            } else if s == S_RID {
                get(&d.id, i)
            } else if s == S_PK {
                get(&d.pk, i)
            } else if s == S_GP {
                get(&gp_b, i)
            } else if s == S_DEP {
                get(&dep_b, i)
            } else {
                0
            };
            rw[B] = bv;
            // account ids
            if s == S_P || s == S_V || s == S_S {
                set_char(&mut rw, bv);
                if i + 1 == len {
                    set_bits(&mut rw, 0, 6, (len as u64).saturating_sub(2));
                    set_bits(&mut rw, 6, 6, 64u64.saturating_sub(len as u64));
                }
            }
            if s == S_P {
                let dd = bv as i128 - get(ld, i) as i128;
                acc_v += sq(dd);
                rw[ACC] = acc_v % PM;
                if i + 1 == len {
                    let l6 = len as i128 - 6;
                    let pv = (acc_v + sq(l6)) % PM;
                    rw[P1] = pv;
                    rw[ISYS] = inv_p(pv);
                }
            }
            if s == S_V {
                acc_v += b2n(is_hex_c(bv));
                rw[ACC] = acc_v;
                let v0 = get(&d.recv, 0);
                let v1 = get(&d.recv, 1);
                rw[VC0] = v0;
                rw[VC1] = v1;
                let h01v = b2n(is_hex_c(v0)) + b2n(is_hex_c(v1));
                rw[H01] = h01v;
                if i + 1 == len {
                    let l = len as i128;
                    let a = acc_v as i128;
                    let (v0, v1, h) = (v0 as i128, v1 as i128, h01v as i128);
                    let pv1 = (sq(l - 64) + sq(a - l)) % PM;
                    let pv2 = (sq(l - 42) + sq(v0 - 48) + sq(v1 - 120) + sq(a - h - 40)) % PM;
                    let pv3 = (sq(l - 42) + sq(v0 - 48) + sq(v1 - 115) + sq(a - h - 40)) % PM;
                    rw[P1] = pv1;
                    rw[P2] = pv2;
                    rw[P3] = pv3;
                    rw[I1] = inv_p(pv1);
                    rw[I2] = inv_p(pv2);
                    rw[I3] = inv_p(pv3);
                }
            }
            // key symbols (slot A)
            if s == S_V {
                rw[G_KA] = 1;
                rw[T_A] = 2 + 2 * i as u64;
                rw[SYM_A] = bv / 16;
            }
            if s == S_VL && i < 2 {
                rw[KZ] = 1;
                rw[G_KA] = 1;
                rw[T_A] = i as u64;
            }
            if s == S_RID && i == 0 {
                rw[G_KA] = 1;
                rw[T_A] = 2 + 2 * lv;
                rw[SYM_A] = SYM_END;
                rw[LAST_A] = 1;
            }
            // digest windows
            if i == 0 && (s == S_XRI || s == S_XLH) {
                rw[G_DG] = 1;
                rw[D_I] = if s == S_XRI { msg_id(K_RID, d.r) } else { msg_id(K_PEO, d.r) };
                rw[D_L] = if s == S_XRI { 48 } else { d.peo_len };
            }
            // gas
            if s == S_GP {
                let (bin, dv, bo) = gp_diff.get(i).copied().unwrap_or((0, 0, 0));
                rw[C1] = bin;
                set_bits(&mut rw, 0, 8, dv);
                set_bits(&mut rw, 8, 1, bo);
                let sb = conv(g5, &p_b, i) + cc2;
                rw[C2] = cc2;
                rw[BURNT] = sb % 256;
                set_bits(&mut rw, 9, 11, sb / 256);
                cc2 = sb / 256;
                let sr = conv(g5, &sur_b, i) + cc3;
                rw[C3] = cc3;
                rw[RAMT] = sr % 256;
                set_bits(&mut rw, 20, 11, sr / 256);
                cc3 = sr / 256;
                let tt = get(&tok_old, i) + sb % 256 + cc4;
                rw[C4] = cc4;
                set_bits(&mut rw, 31, 8, tt % 256);
                set_bits(&mut rw, 39, 1, tt / 256);
                cc4 = tt / 256;
                run_d += dv;
                rw[SUM_D] = run_d;
                if i + 1 == len {
                    rw[INV_A] = if d.hr { inv_p(run_d) } else { 0 };
                }
                for j in 0..4 {
                    rw[dl(j)] = if j < i { get(&p_b, i - 1 - j) } else { 0 };
                    rw[dl(4 + j)] = if j < i { get(&sur_b, i - 1 - j) } else { 0 };
                }
            }
            // balances
            if s == S_DEP {
                rw[BEF] = get(&bef_b, i);
                rw[LK] = get(&lk_b, i);
                rw[ST] = get(&st_b, i);
                let sa = get(&bef_b, i) + get(&dep_b, i) + cc1;
                rw[C1] = cc1;
                set_bits(&mut rw, 0, 8, sa % 256);
                set_bits(&mut rw, 8, 1, sa / 256);
                cc1 = sa / 256;
                run_a += 255 - get(&aft_b, i);
                rw[DSUM] = run_a;
                if i + 1 == len {
                    rw[INV_B] = inv_p(run_a);
                }
                let stt = get(&aft_b, i) + get(&lk_b, i) + cc2;
                rw[C2] = cc2;
                set_bits(&mut rw, 9, 8, stt % 256);
                set_bits(&mut rw, 17, 1, stt / 256);
                cc2 = stt / 256;
                let sqv = conv(&S_LE, &st_b, i) + cc3;
                rw[C3] = cc3;
                set_bits(&mut rw, 18, 8, sqv % 256);
                set_bits(&mut rw, 26, 12, sqv / 256);
                cc3 = sqv / 256;
                let tq = get(&tot_b, i) as i64 - get(&q_b, i) as i64 - cc4 as i64;
                let (dv, bo) = if tq < 0 { ((tq + 256) as u64, 1) } else { (tq as u64, 0) };
                rw[C4] = cc4;
                set_bits(&mut rw, 38, 8, dv);
                set_bits(&mut rw, 46, 1, bo);
                cc4 = bo;
                rw[R1] = b2n(i == 1);
                if i == 1 && !d.big {
                    set_bits(&mut rw, 47, 10, 770u64.saturating_sub(get(&st_b, 0) + 256 * get(&st_b, 1)));
                }
                if i == 0 {
                    set_bits(&mut rw, 57, 9, d.r.saturating_sub(d.tprev));
                }
                for j in 0..7 {
                    rw[dl(j)] = if j < i { get(&st_b, i - 1 - j) } else { 0 };
                }
            }
            rows.push(rw);
        }
    }
    rows
}

/// Claim rows (`RcptGen.claimRows`).
fn claim_rows(pubv: &[u64]) -> Vec<Row> {
    let pubs = |off: usize, len: usize| -> Vec<u64> { (0..len).map(|j| get(pubv, off + j)).collect() };
    let mut a = pubs(PV_SHARD, 8);
    a.extend(pubs(PV_N, 4));
    let bb = pubs(PV_NREF, 4);
    let cc = G_LE.to_vec();
    let dd = pubs(PV_GASLIM, 8);
    let tt = pubs(PV_GAS, 8);
    let n: u64 = pubs(PV_N, 4).iter().rev().fold(0u64, |acc, &x| x + 256 * acc);
    let y_b = le_bytes(8, n.saturating_sub(1) as u128 * GAS_G);
    let mut rows = Vec::with_capacity(12);
    let mut cc1: u64 = 0;
    let mut cc2: u64 = 1;
    let mut cc3: u64 = 0;
    for i in 0..12usize {
        let mut rw = zero_row();
        rw[ACT] = 1;
        rw[S_CL] = 1;
        rw[IDX] = i as u64;
        rw[FS] = b2n(i == 0);
        rw[FE] = b2n(i == 11);
        for j in 0..12 {
            rw[reg(j)] = get(&a, (i + j) % 12);
        }
        for j in 0..4 {
            rw[reg(12 + j)] = get(&bb, (i + j) % 4);
        }
        for j in 0..8 {
            rw[reg(16 + j)] = get(&cc, (i + j) % 8);
            rw[reg(24 + j)] = get(&dd, (i + j) % 8);
            rw[tok(j)] = get(&tt, (i + j) % 8);
        }
        rw[LO8] = b2n(i < 8);
        rw[LO4] = b2n(i < 4);
        if i == 0 {
            rw[INV_A] = inv_p(get(pubv, PV_N) + get(pubv, PV_N + 1));
        }
        if i < 8 {
            let sy = n.saturating_sub(1) * get(&cc, i) + cc1;
            rw[C1] = cc1;
            set_bits(&mut rw, 0, 8, sy % 256);
            set_bits(&mut rw, 8, 8, sy / 256);
            cc1 = sy / 256;
            let td = get(&dd, i) as i64 - get(&y_b, i) as i64 - cc2 as i64;
            let (dv, bo) = if td < 0 { ((td + 256) as u64, 1) } else { (td as u64, 0) };
            rw[C2] = cc2;
            set_bits(&mut rw, 16, 8, dv);
            set_bits(&mut rw, 24, 1, bo);
            cc2 = bo;
            let sg = get(&y_b, i) + get(&cc, i) + cc3;
            rw[C3] = cc3;
            set_bits(&mut rw, 25, 1, sg / 256);
            cc3 = sg / 256;
        }
        rows.push(rw);
    }
    rows
}

// ---------------------------------------------------------------------------
// Emissions (`Tables/Rcpt/Fields.lean`, `emits`)
// ---------------------------------------------------------------------------

/// A linear expression `k + Σ coef·col` (every `emits` expression is one).
#[derive(Clone, Debug)]
struct Lin {
    k: u64,
    t: Vec<(u64, usize)>,
}

impl Lin {
    fn eval(&self, rw: &Row) -> u64 {
        self.t.iter().fold(self.k % PM, |a, &(m, c)| (a + m % PM * (rw[c] % PM)) % PM)
    }
}

fn kk(v: u64) -> Lin {
    Lin { k: v, t: vec![] }
}
fn cc(x: usize) -> Lin {
    Lin { k: 0, t: vec![(1, x)] }
}
/// `sum` of constants and `(coef, col)` terms.
fn lin(k: u64, t: &[(u64, usize)]) -> Lin {
    Lin { k, t: t.to_vec() }
}

/// `(Id, pos, value, gate)`
type Em = [Lin; 4];

/// `emits` of `Tables/Rcpt/Fields.lean`.
fn emits() -> Vec<(usize, Vec<Em>)> {
    let peo = || lin(K_PEO, &[(16, R)]);
    let leaf = || lin(K_LEAF, &[(16, R)]);
    let ridm = || lin(K_RID, &[(16, R)]);
    let rc = || kk(K_RC);
    let rf = || kk(K_RF);
    let ix = || cc(IDX);
    let be = || cc(B);
    let one = || kk(1);
    let hr = || cc(HR);
    // `at' [..]` = `sum (base ++ [ix])`
    let at = |k: u64, t: &[(u64, usize)]| {
        let mut t = t.to_vec();
        t.push((1, IDX));
        Lin { k, t }
    };
    // `varE` = `Lp + Lv + Ls + 32·kt`
    let var: [(u64, usize); 4] = [(1, LP), (1, LV), (1, LS), (32, KT)];
    let with = |a: &[(u64, usize)], b: &[(u64, usize)]| -> Vec<(u64, usize)> { a.iter().chain(b).copied().collect() };
    vec![
        (S_CL, vec![[rc(), ix(), cc(reg(0)), one()], [rf(), ix(), cc(reg(12)), cc(LO4)]]),
        (S_PL, vec![[rc(), at(0, &[(1, O)]), be(), one()]]),
        (S_P, vec![[rc(), at(4, &[(1, O)]), be(), one()]]),
        (
            S_VL,
            vec![[rc(), at(4, &[(1, O), (1, LP)]), be(), one()], [peo(), at(28, &[(32, HR)]), be(), one()]],
        ),
        (
            S_V,
            vec![[rc(), at(8, &[(1, O), (1, LP)]), be(), one()], [peo(), at(32, &[(32, HR)]), be(), one()]],
        ),
        (
            S_RID,
            vec![
                [rc(), at(8, &[(1, O), (1, LP), (1, LV)]), be(), one()],
                [leaf(), at(4, &[]), be(), one()],
                [ridm(), ix(), be(), hr()],
            ],
        ),
        (
            S_T0,
            vec![
                [rc(), lin(40, &[(1, O), (1, LP), (1, LV)]), be(), one()],
                [rf(), lin(46, &[(1, O2), (1, LS)]), be(), hr()],
            ],
        ),
        (
            S_SL,
            vec![
                [rc(), at(41, &[(1, O), (1, LP), (1, LV)]), be(), one()],
                [rf(), at(10, &[(1, O2)]), be(), hr()],
                [rf(), at(47, &[(1, O2), (1, LS)]), be(), hr()],
            ],
        ),
        (
            S_S,
            vec![
                [rc(), at(45, &[(1, O), (1, LP), (1, LV)]), be(), one()],
                [rf(), at(14, &[(1, O2)]), be(), hr()],
                [rf(), at(51, &[(1, O2), (1, LS)]), be(), hr()],
            ],
        ),
        (
            S_KT,
            vec![
                [rc(), lin(45, &[(1, O), (1, LP), (1, LV), (1, LS)]), be(), one()],
                [rf(), lin(51, &[(1, O2), (2, LS)]), be(), hr()],
            ],
        ),
        (
            S_PK,
            vec![
                [rc(), at(46, &[(1, O), (1, LP), (1, LV), (1, LS)]), be(), one()],
                [rf(), at(52, &[(1, O2), (2, LS)]), be(), hr()],
            ],
        ),
        (
            S_GP,
            vec![
                [rc(), at(78, &with(&[(1, O)], &var)), be(), one()],
                [peo(), at(12, &[(32, HR)]), cc(BURNT), one()],
                [rf(), at(113, &[(1, O2), (2, LS), (32, KT)]), cc(RAMT), hr()],
            ],
        ),
        (
            S_TL,
            vec![
                [rc(), at(94, &with(&[(1, O)], &var)), be(), one()],
                [rf(), at(100, &[(1, O2), (2, LS), (32, KT)]), be(), hr()],
            ],
        ),
        (S_DEP, vec![[rc(), at(107, &with(&[(1, O)], &var)), be(), one()]]),
        (S_XP0, vec![[peo(), ix(), be(), one()]]),
        (
            S_XRI,
            vec![[peo(), at(4, &[]), be(), one()], [rf(), at(14, &[(1, O2), (1, LS)]), be(), one()]],
        ),
        (S_XG, vec![[peo(), at(4, &[(32, HR)]), be(), one()]]),
        (S_XST, vec![[peo(), at(32, &[(32, HR), (1, LV)]), be(), one()]]),
        (S_XL0, vec![[leaf(), ix(), be(), one()]]),
        (S_XLH, vec![[leaf(), at(36, &[]), be(), one()]]),
        (S_XRH, vec![[ridm(), at(32, &[]), be(), one()]]),
        (S_XRF, vec![[rf(), at(0, &[(1, O2)]), be(), one()]]),
        (S_XRZ, vec![[rf(), at(84, &[(1, O2), (2, LS), (32, KT)]), be(), one()]]),
    ]
}

/// Fill the emission slots of a row from the table's `emits` (`fillEmits`).
fn fill_emits(ems: &[(usize, Vec<Em>)], rw: &mut Row) {
    for (s, es) in ems {
        if rw[*s] == 1 {
            for (e, em) in es.iter().enumerate() {
                let vals = [em[0].eval(rw), em[1].eval(rw), em[2].eval(rw), em[3].eval(rw)];
                rw[e_id(e)] = vals[0];
                rw[e_pos(e)] = vals[1];
                rw[e_v(e)] = vals[2];
                rw[e_g(e)] = vals[3];
            }
        }
    }
}

/// `clog2`/`logOf`/`padTo` of `Render/Common.lean`.
fn pad_len(n: usize) -> usize {
    let mut l = 0u32;
    while (1usize << l) < n {
        l += 1;
    }
    1usize << l.max(1)
}

/// Rows of the `rcpt` table from the public inputs, `bgp` and the per-receipt
/// data (the body of `rcptRowsAll`), reduced mod `p`.
pub fn rcpt_rows_of(pubv: &[u64], bgp: u128, ds: &[Rd]) -> Vec<Vec<u32>> {
    let bgp_b = le_bytes(16, bgp);
    let mut rows = claim_rows(pubv);
    for d in ds {
        rows.extend(seg_rows(d, pubv, &bgp_b));
    }
    if let Some(last) = rows.last_mut() {
        last[LAST_R] = 1;
    }
    let ems = emits();
    for rw in rows.iter_mut() {
        fill_emits(&ems, rw);
    }
    rows.push(zero_row());
    let h = pad_len(rows.len());
    rows.resize(h, zero_row());
    rows.into_iter().map(|rw| rw.into_iter().map(|v| (v % PM) as u32).collect()).collect()
}

// ---------------------------------------------------------------------------
// Per-receipt data and the table (`rdOf`, `rcptData`, `rcptRowsAll`)
// ---------------------------------------------------------------------------

fn nats(b: &[u8]) -> Vec<u64> {
    b.iter().map(|&x| x as u64).collect()
}

/// `rfLen r'`: length of the refund receipt's encoding (`0` without refund).
fn rf_len(i: &Info, r: usize) -> u64 {
    if has_refund(i, r) {
        let rc = i.e.rc(r);
        let bgp = i.c.block_gas_price;
        gas_refund_receipt(&rc, i.c.block_height as u128, surplus_of(bgp, &rc)).encode().len() as u64
    } else {
        0
    }
}

/// Data of receipt `r` (`rdOf`; `o`, `o2`, `rcnt` are prefix sums over the
/// earlier receipts).
pub fn rd_of(i: &Info, r: usize) -> Rd {
    let e = &i.e;
    let c = &i.c;
    let bgp = c.block_gas_price;
    let rc = e.rc(r);
    let k = e.slot(r);
    let a0 = e.acc0(k);
    let bef = e.amt_at(k, r);
    let hr = has_refund(i, r);
    // big := 10^19 · storage ≤ bef + deposit + locked (exact; sums may reach 2^129)
    let q = STORAGE_PER_BYTE.checked_mul(a0.storage_usage);
    let tot = bef.checked_add(rc.deposit).and_then(|a| a.checked_add(a0.locked));
    let big = match (q, tot) {
        (Some(q), Some(t)) => q <= t,
        (Some(_), None) => true,
        (None, Some(_)) => false,
        (None, None) => panic!("rcpt: storage stake out of range"),
    };
    let peo = peo_bytes(i, r);
    Rd {
        r: r as u64,
        pred: nats(&rc.predecessor_id),
        recv: nats(&rc.receiver_id),
        id: nats(&rc.receipt_id),
        signer: nats(&rc.signer_id),
        kt: rc.signer_pk.tag as u64,
        pk: nats(&rc.signer_pk.data),
        gp: rc.gas_price,
        dep: rc.deposit,
        hr,
        ge: bgp <= rc.gas_price,
        kslot: k as u64,
        tprev: tprev_of(e, r) as u64,
        bef,
        locked: a0.locked,
        stor: a0.storage_usage,
        big,
        burnt: burnt_of(bgp, &rc),
        ramt: surplus_of(bgp, &rc),
        tok0: e.tok_at(c, r),
        o: 12 + (0..r).map(|r2| e.rc(r2).encode().len() as u64).sum::<u64>(),
        o2: 4 + (0..r).map(|r2| rf_len(i, r2)).sum::<u64>(),
        rcnt: (0..r).filter(|&r2| has_refund(i, r2)).count() as u64,
        refund_id: nats(&sha_n(&rid_bytes(i, r))),
        peo_len: peo.len() as u64,
        peo_dig: nats(&sha_n(&peo)),
    }
}

/// Per-receipt data from the records (`rcptData`).
pub fn rcpt_data(i: &Info) -> Vec<Rd> {
    (0..i.n_rcpt()).map(|r| rd_of(i, r)).collect()
}

/// Honest rows of the `rcpt` table (`rcptRowsAll`; padded, at least one
/// padding row).
pub fn rcpt_rows_all(i: &Info) -> Vec<Vec<u32>> {
    let pubv: Vec<u64> = i.c.encode().iter().map(|&b| b as u64).collect();
    rcpt_rows_of(&pubv, i.c.block_gas_price, &rcpt_data(i))
}

/// The SHA messages `rcpt` emits (`rcptMsgs`, `Render/RcptSim.lean`).
pub fn rcpt_msgs(i: &Info) -> Vec<Msg> {
    rcpt_msgs_sim(i)
}
