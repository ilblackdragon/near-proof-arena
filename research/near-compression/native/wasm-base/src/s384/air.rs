//! SHA-512 compression AIR v4 ("T2"): two base-4 words per row, degree 9 (FIPS 180-4 §6.4.2).
//!
//! SHA-384 is the same compression with the SHA-384 IV and a 48-byte truncation, both chosen by
//! the consumer of the interface bus.
//!
//! Why this layout (research/near-compression/results/pq384-sha-air3/README.md):
//! * **Base-4 digits, degree 9.**  A 2-bit digit's bit signs are cubic in the digit, so an XOR3
//!   (Σ0, Σ1, σ0, σ1) or Maj of three bits is degree 9 (base 8 gives 21; degree 8 would need about
//!   43 cells per word instead of 32).  NvAir is degree 8, so the final layer's round polynomials
//!   go from 22 to 10 coefficients.
//! * **Two words per row, one word type per row.**  A segment is 128 rows: 42 A rows (a pairs),
//!   42 E rows (e pairs), 40 W rows (message-schedule pairs) and 4 O rows (output pairs).  Every
//!   row has the same 64 digit columns, so the AIR opens 64 digit columns (all read at the next
//!   row) instead of 132 + 132.  A two-row window holds four consecutive words of one type, which
//!   is exactly what Maj/Ch need (three consecutive words) and what Σ/σ need (one word).
//! * **Everything that is not a range check is a bus message.**  Degree-9 values (round
//!   partials, Σ/σ residuals) travel as interaction messages with kind-gated counts, so no
//!   constraint multiplies a degree-9 expression by a flag.  Values from other rows are stored in
//!   15 aux columns whose meaning depends on the row kind; every addition is checked as a residual
//!   matched by exactly one sender (carries stored), so each remote 64-bit operand costs 3 cells.
//! * **K is folded into h for free.**  The E rows store h + K limbwise (unreduced) and a lookup
//!   against the control/K table checks (stored − h) = K, so the round constant needs no cells.
//!
//! Layout, equations and the faithfulness argument: README.md and FAITHFUL-v4.md next to it.
#![allow(clippy::needless_range_loop)]
use openvm_stark_backend::{PartitionedBaseAir, interaction::InteractionBuilder};
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, BaseAirWithPublicValues};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::Matrix;

pub const ROWS: usize = 128;
/// First row of each block inside a segment.
pub const AB: usize = 0;
pub const EB: usize = 42;
pub const WB: usize = 84;
pub const OB: usize = 124;

/// Digits per word (base 4) and column layout.
pub const ND: usize = 32;
pub const D0: usize = 0;
pub const D1: usize = ND;
pub const XA: usize = 2 * ND;
pub const NX: usize = 15;
pub const C_R: usize = XA + NX;
pub const C_G: usize = C_R + 1;
pub const C_K1: usize = C_R + 2;
pub const C_K2: usize = C_R + 3;
pub const WIDTH: usize = C_R + 4;
/// Interface / addition limbs: bits [0, 21), [21, 42), [42, 64) (as v2.1 k = 3).
pub const LIMB_OFF: [usize; 4] = [0, 21, 42, 64];
pub const CARRY_RANGE: u64 = 8;
/// Offset of the (signed) carries of the a = e + M - d check.
pub const OFF_A: i64 = 4;
/// Kind digits range over 0..KD.
pub const KD: u64 = 5;
/// Maximum constraint degree (XOR3 / Maj of three cubic bit signs).
pub const DEGREE: usize = 9;

pub const BUS_CTL: u16 = 100;
pub const BUS_K: u16 = 101;
pub const BUS_LB: u16 = 102;
pub const BUS_IF: u16 = 103;
/// Lookback-bus tags (messages are keyed by the sender's global row).
pub const TP: u64 = 1; // a row's two slot words
pub const T1: u64 = 2; // slot 1 word
pub const TF: u64 = 3; // forwarded d + W
pub const TY: u64 = 4; // (M - d) of the out-round, d of the in-round (A)
pub const TL: u64 = 5; // Σ1 + Ch of the out-round (E)
pub const TV: u64 = 6; // V = W[t-16] + σ0(W[t-15]) pair (W)
pub const TW7: u64 = 7; // W[t-7] pair (W)

pub const K: [u64; 80] = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];

// ------------------------------------------------------------------------------------------
// Row kinds
// ------------------------------------------------------------------------------------------

/// Row kind, fixed by the row index r inside the segment (control table).  The suffixes are
/// the block-relative index j (A_j: r = j, E_j: r = 42 + j, W_j: r = 84 + j, O_k: r = 124 + k).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Kind {
    Pad,
    A0,
    A1,
    /// A_2 .. A_39
    AMid,
    A40,
    A41,
    E0,
    E1,
    /// E_2 .. E_39
    EMid,
    E40,
    E41,
    /// W_0 .. W_3: interface, V sender
    Wa,
    /// W_4 .. W_6: interface, V and W7 sender
    Wb,
    /// W_7: interface, V and W7 sender, schedule check
    Wc,
    /// W_8 .. W_31: V and W7 sender, schedule check
    Wd,
    /// W_32 .. W_35: W7 sender, schedule check
    We,
    /// W_36 .. W_38: schedule check
    Wf,
    /// W_39
    Wg,
    O,
}
use Kind::*;

pub const REAL_KINDS: [Kind; 18] =
    [A0, A1, AMid, A40, A41, E0, E1, EMid, E40, E41, Wa, Wb, Wc, Wd, We, Wf, Wg, O];

impl Kind {
    /// Kind digits (k1, k2), each in 0..KD; padding is (0, 0).
    pub fn code(self) -> (u64, u64) {
        match self {
            Pad => (0, 0),
            A0 => (1, 0),
            A1 => (1, 1),
            AMid => (1, 2),
            A40 => (1, 3),
            A41 => (1, 4),
            E0 => (2, 0),
            E1 => (2, 1),
            EMid => (2, 2),
            E40 => (2, 3),
            E41 => (2, 4),
            Wa => (3, 0),
            Wb => (3, 1),
            Wc => (3, 2),
            Wd => (3, 3),
            We => (3, 4),
            Wf => (4, 0),
            Wg => (4, 1),
            O => (4, 2),
        }
    }
    pub fn is_a(self) -> bool {
        matches!(self, A0 | A1 | AMid | A40 | A41)
    }
    pub fn is_e(self) -> bool {
        matches!(self, E0 | E1 | EMid | E40 | E41)
    }
    pub fn is_w(self) -> bool {
        matches!(self, Wa | Wb | Wc | Wd | We | Wf | Wg)
    }
}

/// Kind of segment row r.
pub fn kind_of(r: usize) -> Kind {
    match r {
        0 => A0,
        1 => A1,
        2..=39 => AMid,
        40 => A40,
        41 => A41,
        42 => E0,
        43 => E1,
        44..=81 => EMid,
        82 => E40,
        83 => E41,
        84..=87 => Wa,
        88..=90 => Wb,
        91 => Wc,
        92..=115 => Wd,
        116..=119 => We,
        120..=122 => Wf,
        123 => Wg,
        124..=127 => O,
        _ => panic!("row {r} outside a segment"),
    }
}

/// Per-kind roles: counts of every interaction and the receive keys.  `None` = not active.
#[derive(Clone, Copy, Debug, Default)]
pub struct Roles {
    pub iface: bool,
    /// send of the slot pair (g, TP, s0, s1); value = number of receivers
    pub s_pair: u64,
    /// send of slot 1 (g, T1, s1) and of the forward (g, TF, s0 + X[12..15])
    pub s_slot1_fwd: bool,
    /// window sends
    pub s_y: bool,
    pub s_l: bool,
    pub s_v: bool,
    pub s_w7: bool,
    pub k_lookup: bool,
    /// R1: receive into X[0..6] with (key offset, tag)
    pub r1: Option<(i64, u64)>,
    /// R2: receive into X[12..15]
    pub r2: Option<(i64, u64)>,
    /// R3: A check (residual vs E pair at g + 43)
    pub r_a: bool,
    /// R4/R5: E checks (residuals vs the forwards at g - 43 and g + 41)
    pub r_e: bool,
    /// R6: W check (residual vs W7 at g - 3)
    pub r_w: bool,
    /// R7: feed-forward check (residual vs the O row's pair at g + offset)
    pub r_ff: Option<i64>,
    /// aux columns in use: X[0..6], X[6..12], X[12..15]
    pub x_lo: bool,
    pub x_mid: bool,
    pub x_hi: bool,
}

pub fn roles(k: Kind) -> Roles {
    let mut z = Roles::default();
    match k {
        Pad => {}
        A0 => {
            z.iface = true;
            z.s_slot1_fwd = true;
            z.s_y = true;
            z.r1 = Some((40, TP));
            z.r2 = Some((84, T1));
            z.r_ff = Some(125);
        }
        A1 | AMid => {
            z.iface = k == A1;
            z.s_pair = (k == A1) as u64;
            z.s_slot1_fwd = true;
            z.s_y = true;
            z.r1 = Some((-1, TY));
            z.r2 = Some((84, T1));
            z.r_a = true;
        }
        A40 => {
            z.s_pair = 1;
            z.r1 = Some((-1, TY));
            z.r_a = true;
        }
        A41 => {
            z.r1 = Some((-40, TP));
            z.r_ff = Some(83);
        }
        E0 => {
            z.iface = true;
            z.s_l = true;
            z.k_lookup = true;
            z.r1 = Some((40, TP));
            z.r_ff = Some(85);
        }
        E1 | EMid => {
            z.iface = k == E1;
            z.s_pair = 1;
            z.s_l = true;
            z.k_lookup = true;
            z.r2 = Some((-1, TL));
            z.r_e = true;
        }
        E40 => {
            z.s_pair = 2;
            z.r2 = Some((-1, TL));
            z.r_e = true;
        }
        E41 => {
            z.s_pair = 1;
            z.r1 = Some((-40, TP));
            z.r_ff = Some(43);
        }
        Wa | Wb | Wc | Wd | We | Wf | Wg => {
            z.iface = matches!(k, Wa | Wb | Wc);
            z.s_slot1_fwd = true;
            z.r2 = Some((-84, T1));
            z.s_v = matches!(k, Wa | Wb | Wc | Wd);
            z.s_w7 = matches!(k, Wb | Wc | Wd | We);
            if matches!(k, Wc | Wd | We | Wf) {
                z.r1 = Some((-7, TV));
                z.r_w = true;
            }
        }
        O => {
            z.iface = true;
            z.s_pair = 1;
        }
    }
    // E rows 1..40 hold h'' and h' in X[0..6] (pinned by the K lookup of the window before)
    let e_h = matches!(k, E1 | EMid | E40);
    z.x_lo = z.r1.is_some() || e_h;
    z.x_mid = z.r_a || z.r_e || z.r_w || z.r_ff.is_some();
    z.x_hi = z.r2.is_some();
    z
}

/// Interface pair index sent by segment row r (if any).
pub fn iface_idx(r: usize) -> Option<u64> {
    match kind_of(r) {
        A0 => Some(1),
        A1 => Some(0),
        E0 => Some(3),
        E1 => Some(2),
        Wa | Wb | Wc => Some((r - WB) as u64 + 4),
        O => Some((r - OB) as u64 + 12),
        _ => None,
    }
}

/// Control entry of table index i (< 128): (r, k1, k2).
pub fn ctl_entry(i: usize) -> [u64; 3] {
    let (a, b) = kind_of(i).code();
    [i as u64, a, b]
}

/// K entry of table index i: (r, K limbs of rounds 2(i - 42), 2(i - 42) + 1) for the E window
/// senders i in [42, 82), else (r, 0...).
pub fn k_entry(i: usize) -> [u64; 7] {
    let mut e = [0u64; 7];
    e[0] = i as u64;
    if (EB..EB + 40).contains(&i) {
        let t = 2 * (i - EB);
        e[1..4].copy_from_slice(&limbs(K[t]));
        e[4..7].copy_from_slice(&limbs(K[t + 1]));
    }
    e
}

pub fn lw(l: usize) -> usize {
    LIMB_OFF[l + 1] - LIMB_OFF[l]
}
pub fn limbs(x: u64) -> [u64; 3] {
    std::array::from_fn(|l| (x >> LIMB_OFF[l]) & ((1u64 << lw(l)) - 1))
}
pub fn digits(x: u64) -> [u64; ND] {
    std::array::from_fn(|j| (x >> (2 * j)) & 3)
}

// ------------------------------------------------------------------------------------------
// Bit signs over symbolic or concrete expressions (as v2.1, digit width 2)
// ------------------------------------------------------------------------------------------
//
// A bit b is carried as its sign σ = 1 - 2b.  For a 2-bit digit v, every bit sign is an odd
// cubic in u = v - 3/2: σ_t = u (α_t + β_t u²).  XOR is a product of signs.

fn rx<E: PrimeCharacteristicRing + Clone>(x: &[E], r1: usize, r2: usize, r3: usize, shr: bool) -> Vec<E> {
    (0..64)
        .map(|i| {
            let ab = x[(i + r1) % 64].clone() * x[(i + r2) % 64].clone();
            if shr && i + r3 >= 64 { ab } else { ab * x[(i + r3) % 64].clone() }
        })
        .collect()
}
pub fn big_sigma0<E: PrimeCharacteristicRing + Clone>(a: &[E]) -> Vec<E> {
    rx(a, 28, 34, 39, false)
}
pub fn big_sigma1<E: PrimeCharacteristicRing + Clone>(e: &[E]) -> Vec<E> {
    rx(e, 14, 18, 41, false)
}
pub fn small_sigma0<E: PrimeCharacteristicRing + Clone>(w: &[E]) -> Vec<E> {
    rx(w, 1, 8, 7, true)
}
pub fn small_sigma1<E: PrimeCharacteristicRing + Clone>(w: &[E]) -> Vec<E> {
    rx(w, 19, 61, 6, true)
}
/// 2 x sign of Ch(e, f, g):  σf + σg + σe (σg - σf).
pub fn ch2<E: PrimeCharacteristicRing + Clone>(e: &[E], f: &[E], g: &[E]) -> Vec<E> {
    (0..64)
        .map(|i| f[i].clone() + g[i].clone() + e[i].clone() * (g[i].clone() - f[i].clone()))
        .collect()
}
/// 2 x sign of Maj(a, b, c):  σa + σb + σc - σa σb σc.
pub fn maj2<E: PrimeCharacteristicRing + Clone>(a: &[E], b: &[E], c: &[E]) -> Vec<E> {
    (0..64)
        .map(|i| a[i].clone() + b[i].clone() + c[i].clone() - a[i].clone() * b[i].clone() * c[i].clone())
        .collect()
}

/// (α_lo, β_lo, α_hi, β_hi) with σ_t(v) = u (α_t + β_t u²), u = v - 3/2.
pub fn sign_coefs<F: Field>() -> [F; 4] {
    // σ_lo: v = 2 -> +1, v = 3 -> -1;  σ_hi: v = 2 -> -1, v = 3 -> -1  (odd in u)
    let solve = |y_half: F, y_three_half: F| {
        // u = 1/2: (1/2)(α + β/4) = y1 ;  u = 3/2: (3/2)(α + 9β/4) = y2
        let two = F::from_u32(2);
        let a1 = y_half * two; // α + β/4
        let a2 = y_three_half * two * F::from_u32(3).inverse(); // α + 9β/4
        let beta = (a2 - a1) * two.inverse(); // (9/4 - 1/4) β = 2β
        let alpha = a1 - beta * F::from_u32(4).inverse();
        (alpha, beta)
    };
    let (al, bl) = solve(F::ONE, -F::ONE);
    let (ah, bh) = solve(-F::ONE, -F::ONE);
    [al, bl, ah, bh]
}

/// One word's bit signs (64, LSB first) and its three limbs.
pub struct Word<E> {
    pub sg: Vec<E>,
    pub limbs: [E; 3],
}

/// Bit signs and limbs of the word whose 32 digits are `d`.  The limb boundary at bit 21
/// splits digit 10; its bits are (1 - σ)/2, cubic in the digit.
pub fn word<F: Field, E: PrimeCharacteristicRing + Clone + From<F>>(coef: &[F; 4], d: &[E]) -> Word<E> {
    let half = F::from_u32(2).inverse();
    let c = F::from_u32(3) * half;
    let mut sg = Vec::with_capacity(64);
    for v in d.iter().take(ND) {
        let u = v.clone() - E::from(c);
        let w = u.clone() * u.clone();
        sg.push(u.clone() * (E::from(coef[0]) + w.clone() * E::from(coef[1])));
        sg.push(u * (E::from(coef[2]) + w * E::from(coef[3])));
    }
    let bit = |s: &E| (E::ONE - s.clone()) * E::from(half);
    let mut l0 = E::ZERO;
    for j in 0..10 {
        l0 += d[j].clone() * E::from_u64(1u64 << (2 * j));
    }
    l0 += bit(&sg[20]) * E::from_u64(1u64 << 20);
    let mut l1 = bit(&sg[21]);
    for j in 11..21 {
        l1 += d[j].clone() * E::from_u64(1u64 << (2 * j - 21));
    }
    let mut l2 = E::ZERO;
    for j in 21..ND {
        l2 += d[j].clone() * E::from_u64(1u64 << (2 * j - 42));
    }
    Word { sg, limbs: [l0, l1, l2] }
}

/// Limbs of the word whose bit signs are `scale * raw[b]`:
/// limb = sum 2^{b-off} (1 - σ_b) / 2 = (2^w - 1)/2 - scale/2 sum 2^{b-off} raw_b.
pub fn limbs_of_signs<F: Field, E: PrimeCharacteristicRing + Clone + From<F>>(raw: &[E], scale: F) -> [E; 3] {
    let half = F::from_u32(2).inverse();
    std::array::from_fn(|l| {
        let (lo, hi) = (LIMB_OFF[l], LIMB_OFF[l + 1]);
        let mut acc = E::from(F::from_u64((1u64 << (hi - lo)) - 1) * half);
        for b in lo..hi {
            acc -= raw[b].clone() * E::from(F::from_u64(1u64 << (b - lo)) * half * scale);
        }
        acc
    })
}

pub fn add3<E: PrimeCharacteristicRing + Clone>(xs: &[&[E; 3]]) -> [E; 3] {
    std::array::from_fn(|i| xs.iter().fold(E::ZERO, |a, x| a + x[i].clone()))
}
pub fn sub3<E: PrimeCharacteristicRing + Clone>(x: &[E; 3], y: &[E; 3]) -> [E; 3] {
    std::array::from_fn(|i| x[i].clone() - y[i].clone())
}
fn cols3<E: Clone>(row: &[E], c: usize) -> [E; 3] {
    std::array::from_fn(|i| row[c + i].clone())
}
/// out_i + 2^{w_i}(c_i - off) - (c_{i-1} - off): the left side of a limbwise addition check.
pub fn lhs<E: PrimeCharacteristicRing + Clone>(out: &[E; 3], carry: &[E; 3], off: i64) -> [E; 3] {
    let o = E::from_i64(off);
    std::array::from_fn(|i| {
        let mut v = out[i].clone() + (carry[i].clone() - o.clone()) * E::from_u64(1u64 << lw(i));
        if i > 0 {
            v -= carry[i - 1].clone() - o.clone();
        }
        v
    })
}
/// sum - (2^{w_i} c_i - c_{i-1}): the output limbs of `sum` with carries c (offset 0).
pub fn reduce<E: PrimeCharacteristicRing + Clone>(sum: &[E; 3], carry: &[E; 3]) -> [E; 3] {
    std::array::from_fn(|i| {
        let mut v = sum[i].clone() - carry[i].clone() * E::from_u64(1u64 << lw(i));
        if i > 0 {
            v += carry[i - 1].clone();
        }
        v
    })
}

/// Lagrange basis polynomial of node a over {0, .., KD - 1}, evaluated at x.
pub fn lagrange<F: Field, E: PrimeCharacteristicRing + Clone + From<F>>(x: &E, a: u64) -> E {
    let mut num = E::ONE;
    let mut den = F::ONE;
    for m in 0..KD {
        if m != a {
            num *= x.clone() - E::from_u64(m);
            den *= F::from_u64(a) - F::from_u64(m);
        }
    }
    num * E::from(den.inverse())
}

// ------------------------------------------------------------------------------------------
// The compression AIR
// ------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub struct Sha512Air4;
impl<F> BaseAir<F> for Sha512Air4 {
    fn width(&self) -> usize {
        WIDTH
    }
}
impl<F> PartitionedBaseAir<F> for Sha512Air4 {}
impl<F> BaseAirWithPublicValues<F> for Sha512Air4 {}

impl<AB: AirBuilderWithPublicValues + InteractionBuilder> Air<AB> for Sha512Air4 {
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        let l: Vec<AB::Expr> = main.row_slice(0).unwrap().iter().map(|&v| v.into()).collect();
        let n: Vec<AB::Expr> = main.row_slice(1).unwrap().iter().map(|&v| v.into()).collect();
        let one = AB::Expr::ONE;
        let c = |v: u64| AB::Expr::from_u64(v);
        let ci = |v: i64| AB::Expr::from_i64(v);

        // ---- kinds: selectors are products of two degree-4 Lagrange polynomials ----
        let lag1: Vec<AB::Expr> = (0..KD).map(|a| lagrange::<AB::F, AB::Expr>(&l[C_K1], a)).collect();
        let lag2: Vec<AB::Expr> = (0..KD).map(|a| lagrange::<AB::F, AB::Expr>(&l[C_K2], a)).collect();
        let sel = |k: Kind| -> AB::Expr {
            let (a, bb) = k.code();
            lag1[a as usize].clone() * lag2[bb as usize].clone()
        };
        let pad_l = lag1[0].clone();
        let pad_n = lagrange::<AB::F, AB::Expr>(&n[C_K1], 0);
        let real_l = one.clone() - pad_l.clone();
        // sum of selectors over the kinds satisfying `f`, weighted by `w`
        let sum = |f: &dyn Fn(Kind) -> AB::Expr| -> AB::Expr {
            REAL_KINDS.iter().fold(AB::Expr::ZERO, |acc, &k| acc + f(k))
        };
        let count = |f: &dyn Fn(&Roles) -> u64| -> AB::Expr {
            sum(&|k| {
                let m = f(&roles(k));
                if m == 0 { AB::Expr::ZERO } else { sel(k) * c(m) }
            })
        };

        // ---- range checks and zero rules ----
        for col in [C_K1, C_K2] {
            let v = l[col].clone();
            let mut p = v.clone();
            for m in 1..KD {
                p *= v.clone() - c(m);
            }
            b.assert_zero(p);
        }
        let coef = sign_coefs::<AB::F>();
        {
            let c32 = AB::Expr::from(AB::F::from_u32(3) * AB::F::from_u32(2).inverse());
            let q1 = AB::Expr::from(AB::F::from_u32(4).inverse());
            let q9 = AB::Expr::from(AB::F::from_u32(9) * AB::F::from_u32(4).inverse());
            for col in 0..2 * ND {
                let u = l[col].clone() - c32.clone();
                let w = u.clone() * u;
                b.assert_zero((w.clone() - q1.clone()) * (w - q9.clone()));
            }
        }
        for col in XA + 6..XA + 12 {
            let v = l[col].clone();
            let mut p = v.clone();
            for m in 1..CARRY_RANGE {
                p *= v.clone() - c(m);
            }
            b.assert_zero(p);
        }
        // padding rows are all zero
        b.assert_zero(pad_l.clone() * l[C_K2].clone());
        for col in (0..XA + NX).chain([C_R, C_G]) {
            b.assert_zero(pad_l.clone() * l[col].clone());
        }
        // aux groups unused by the row's kind are zero
        let unused_lo = sum(&|k| if roles(k).x_lo { AB::Expr::ZERO } else { sel(k) });
        let unused_mid = sum(&|k| if roles(k).x_mid { AB::Expr::ZERO } else { sel(k) });
        let unused_hi = sum(&|k| if roles(k).x_hi { AB::Expr::ZERO } else { sel(k) });
        for i in 0..NX {
            let u = if i < 6 { &unused_lo } else if i < 12 { &unused_mid } else { &unused_hi };
            b.assert_zero(u.clone() * l[XA + i].clone());
        }

        // ---- row sequencing: segments of 128 rows back to back from row 0, then zero rows ----
        let last = c(ROWS as u64 - 1);
        b.when_first_row().assert_zero(l[C_R].clone());
        b.when_first_row().assert_zero(l[C_G].clone());
        // k1 != 0 exactly on real rows (kind digits), so k1 / k1' serve as real flags of degree 1
        let (k1l, k1n) = (l[C_K1].clone(), n[C_K1].clone());
        b.when_last_row().assert_zero(k1l.clone() * (l[C_R].clone() - last.clone()));
        {
            let (r, g) = (C_R, C_G);
            let mut t = b.when_transition();
            t.assert_zero(k1n.clone() * (n[g].clone() - l[g].clone() - one.clone()));
            t.assert_zero(k1n.clone() * (n[r].clone() - l[r].clone() - one.clone()) * n[r].clone());
            t.assert_zero(k1n.clone() * (n[r].clone() - l[r].clone() - one.clone()) * (l[r].clone() - last.clone()));
            t.assert_zero(k1l.clone() * pad_n.clone() * (l[r].clone() - last));
            t.assert_zero(pad_l.clone() * k1n);
        }

        // ---- words ----
        let wd = |row: &[AB::Expr], base: usize| word::<AB::F, AB::Expr>(&coef, &row[base..base + ND]);
        let (l0, l1, n0, n1) = (wd(&l, D0), wd(&l, D1), wd(&n, D0), wd(&n, D1));
        let one_f = AB::F::ONE;
        let half_f = AB::F::from_u32(2).inverse();
        let lb = |sg: &[AB::Expr]| limbs_of_signs::<AB::F, AB::Expr>(sg, one_f);
        let lb2 = |sg: &[AB::Expr]| limbs_of_signs::<AB::F, AB::Expr>(sg, half_f);
        let x3 = |i: usize| cols3(&l, XA + i);
        let xn3 = |i: usize| cols3(&n, XA + i);
        let g = l[C_G].clone();
        let r = l[C_R].clone();

        // ---- control and K lookups (TableAir4) ----
        b.push_interaction(BUS_CTL, vec![r.clone(), l[C_K1].clone(), l[C_K2].clone()], real_l.clone(), 1);
        {
            let mut msg = vec![r.clone()];
            msg.extend(sub3(&xn3(0), &l0.limbs));
            msg.extend(sub3(&xn3(3), &l1.limbs));
            b.push_interaction(BUS_K, msg, count(&|z| z.k_lookup as u64), 1);
        }

        // ---- interface: (cid, pair index, word 2m, word 2m + 1) = (cid, idx, s1, s0) ----
        {
            let cid = g.clone() - r.clone();
            let idx = sel(A0) * c(1) + sel(E0) * c(3) + sel(E1) * c(2)
                + (sel(Wa) + sel(Wb) + sel(Wc)) * (r.clone() - c(WB as u64 - 4))
                + sel(O) * (r.clone() - c(OB as u64 - 12));
            let mut msg = vec![cid, idx];
            msg.extend(l1.limbs.iter().cloned());
            msg.extend(l0.limbs.iter().cloned());
            b.push_interaction(BUS_IF, msg, count(&|z| z.iface as u64), 1);
        }

        // ---- lookback bus (permutation), messages keyed by the sender's global row ----
        let send = |b: &mut AB, key: AB::Expr, tag: AB::Expr, fields: Vec<AB::Expr>, m: AB::Expr| {
            let mut msg = vec![key, tag];
            msg.extend(fields);
            b.push_interaction(BUS_LB, msg, m, 1);
        };
        let flat = |xs: &[&[AB::Expr; 3]]| -> Vec<AB::Expr> { xs.iter().flat_map(|x| x.iter().cloned()).collect() };

        // S1: the row's slot pair, once per receiver
        send(b, g.clone(), c(TP), flat(&[&l0.limbs, &l1.limbs]), count(&|z| z.s_pair));
        // S3, S4: slot 1, and the forward s0 + X[12..15] (A: d_2j + W_2j, W: W_2j+1 + d_2j+1)
        let m_sf = count(&|z| z.s_slot1_fwd as u64);
        send(b, g.clone(), c(T1), flat(&[&l1.limbs]), m_sf.clone());
        send(b, g.clone(), c(TF), flat(&[&add3(&[&l0.limbs, &x3(12)])]), m_sf);
        // S6 (A window): Y = Σ0(n1) + Maj(n1, n0, l1) - l0 for the out-round of row n's check,
        // and d_in = l1 for its in-round.
        {
            let y = sub3(&add3(&[&lb(&big_sigma0(&n1.sg)), &lb2(&maj2(&n1.sg, &n0.sg, &l1.sg))]), &l0.limbs);
            send(b, g.clone(), c(TY), flat(&[&y, &l1.limbs]), count(&|z| z.s_y as u64));
        }
        // S7 (E window): L = Σ1(n1) + Ch(n1, n0, l1) for the out-round of row n's check
        {
            let lo = add3(&[&lb(&big_sigma1(&n1.sg)), &lb2(&ch2(&n1.sg, &n0.sg, &l1.sg))]);
            send(b, g.clone(), c(TL), flat(&[&lo]), count(&|z| z.s_l as u64));
        }
        // S8 (W window): V for the row 7 ahead: (l1 + σ0(l0), l0 + σ0(n1))
        {
            let v0 = add3(&[&l1.limbs, &lb(&small_sigma0(&l0.sg))]);
            let v1 = add3(&[&l0.limbs, &lb(&small_sigma0(&n1.sg))]);
            send(b, g.clone(), c(TV), flat(&[&v0, &v1]), count(&|z| z.s_v as u64));
        }
        // S9 (W window): W[t-7] pair for the row 3 ahead: (l0, n1)
        send(b, g.clone(), c(TW7), flat(&[&l0.limbs, &n1.limbs]), count(&|z| z.s_w7 as u64));

        // R1, R2: stored receives (kind-dependent key offset and tag)
        {
            let key1 = g.clone() + sum(&|k| match roles(k).r1 { Some((o, _)) if o != 0 => sel(k) * ci(o), _ => AB::Expr::ZERO });
            let tag1 = sum(&|k| match roles(k).r1 { Some((_, t)) => sel(k) * c(t), _ => AB::Expr::ZERO });
            let m1 = count(&|z| z.r1.is_some() as u64);
            let mut f = Vec::new();
            for i in 0..6 {
                f.push(l[XA + i].clone());
            }
            send(b, key1, tag1, f, -m1);
            let key2 = g.clone() + sum(&|k| match roles(k).r2 { Some((o, _)) if o != 0 => sel(k) * ci(o), _ => AB::Expr::ZERO });
            let tag2 = sum(&|k| match roles(k).r2 { Some((_, t)) => sel(k) * c(t), _ => AB::Expr::ZERO });
            let m2 = count(&|z| z.r2.is_some() as u64);
            send(b, key2, tag2, flat(&[&x3(12)]), -m2);
        }
        // R3 (A check, rounds 2j-2 / 2j-1 with outputs n0 / n1):
        //   n0 = e + Y            (Y = M - d stored in X[0..3])
        //   n1 = e + M_in - d_in  (M_in = Σ0(n0) + Maj(n0, l1, l0), d_in in X[3..6])
        // residuals matched against the E pair (e_2j-2, e_2j-1) sent by row g + 43.
        {
            let m_in = add3(&[&lb(&big_sigma0(&n0.sg)), &lb2(&maj2(&n0.sg, &l1.sg, &l0.sg))]);
            let res_out = sub3(&lhs(&n0.limbs, &x3(6), OFF_A), &x3(0));
            let res_in = add3(&[&sub3(&lhs(&n1.limbs, &x3(9), OFF_A), &m_in), &x3(3)]);
            send(b, g.clone() + c(43), c(TP), flat(&[&res_out, &res_in]), -count(&|z| z.r_a as u64));
        }
        // R4, R5 (E check, rounds 2j-2 / 2j-1 with outputs n0 / n1):
        //   n0 = h'' + L_out + dW   (h'' = h + K in X[0..3], L_out in X[12..15]; dW from A at g - 43)
        //   n1 = h'  + L_in  + dW   (h' = h + K in X[3..6], L_in = Σ1(n0) + Ch(n0, l1, l0); dW from W at g + 41)
        {
            let m_e = count(&|z| z.r_e as u64);
            let r4 = sub3(&sub3(&lhs(&n0.limbs, &x3(6), 0), &x3(0)), &x3(12));
            send(b, g.clone() - c(43), c(TF), flat(&[&r4]), -m_e.clone());
            let l_in = add3(&[&lb(&big_sigma1(&n0.sg)), &lb2(&ch2(&n0.sg, &l1.sg, &l0.sg))]);
            let r5 = sub3(&sub3(&lhs(&n1.limbs, &x3(9), 0), &x3(3)), &l_in);
            send(b, g.clone() + c(41), c(TF), flat(&[&r5]), -m_e);
        }
        // R6 (W check): n1 = σ1(l1) + V0 + W7_0, n0 = σ1(l0) + V1 + W7_1 (V in X[0..6]);
        // residuals matched against the W7 pair sent by row g - 3.
        {
            let r0 = sub3(&sub3(&lhs(&n1.limbs, &x3(6), 0), &lb(&small_sigma1(&l1.sg))), &x3(0));
            let r1 = sub3(&sub3(&lhs(&n0.limbs, &x3(9), 0), &lb(&small_sigma1(&l0.sg))), &x3(3));
            send(b, g.clone() - c(3), c(TW7), flat(&[&r0, &r1]), -count(&|z| z.r_w as u64));
        }
        // R7 (feed-forward on A0, A41, E0, E41): slot i + X[3i..3i+3] reduced with carries
        // X[6..12] equals slot i of the O row (its pair, sent with TP).
        {
            let ff0 = reduce(&add3(&[&l0.limbs, &x3(0)]), &x3(6));
            let ff1 = reduce(&add3(&[&l1.limbs, &x3(3)]), &x3(9));
            let key = g.clone() + sum(&|k| match roles(k).r_ff { Some(o) => sel(k) * ci(o), None => AB::Expr::ZERO });
            send(b, key, c(TP), flat(&[&ff0, &ff1]), -count(&|z| z.r_ff.is_some() as u64));
        }
    }
}

// ------------------------------------------------------------------------------------------
// Control + K table
// ------------------------------------------------------------------------------------------

/// 128 rows, one per segment row index.  Columns: 7 index bits (a binary counter pinned by the
/// first-row and transition constraints) and the two multiplicities.  Every offered field is
/// the multilinear extension of its 128 values in the index bits (degree <= 7), so the table
/// content is fixed without a preprocessed commitment.
#[derive(Clone, Copy, Debug)]
pub struct TableAir4;
pub const T_BITS: usize = 7;
pub const T_MC: usize = 7;
pub const T_MK: usize = 8;
pub const T_WIDTH: usize = 9;

/// Multilinear extension of `vals` (length 2^bits.len()) at the bit expressions (LSB first).
pub fn mle<E: PrimeCharacteristicRing + Clone>(bits: &[E], vals: &[u64]) -> E {
    let mut cur: Vec<Option<E>> = vals.iter().map(|&v| Some(E::from_u64(v))).collect();
    let mut cv: Vec<u64> = vals.to_vec();
    for bit in bits {
        let mut nxt = Vec::with_capacity(cur.len() / 2);
        let mut nv = Vec::with_capacity(cur.len() / 2);
        for i in 0..cur.len() / 2 {
            let (a, bb) = (cur[2 * i].clone().unwrap(), cur[2 * i + 1].clone().unwrap());
            if cv[2 * i] == cv[2 * i + 1] && cv[2 * i] != u64::MAX {
                nxt.push(Some(a));
                nv.push(cv[2 * i]);
            } else {
                nxt.push(Some(a.clone() + bit.clone() * (bb - a)));
                nv.push(u64::MAX);
            }
        }
        cur = nxt;
        cv = nv;
    }
    cur.pop().unwrap().unwrap()
}

impl<F> BaseAir<F> for TableAir4 {
    fn width(&self) -> usize {
        T_WIDTH
    }
}
impl<F> PartitionedBaseAir<F> for TableAir4 {}
impl<F> BaseAirWithPublicValues<F> for TableAir4 {}
impl<AB: AirBuilderWithPublicValues + InteractionBuilder> Air<AB> for TableAir4 {
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        let l: Vec<AB::Expr> = main.row_slice(0).unwrap().iter().map(|&v| v.into()).collect();
        let n: Vec<AB::Expr> = main.row_slice(1).unwrap().iter().map(|&v| v.into()).collect();
        for i in 0..T_BITS {
            b.assert_bool(l[i].clone());
            b.when_first_row().assert_zero(l[i].clone());
        }
        {
            // binary increment: bit i flips iff all lower bits are 1
            let mut t = b.when_transition();
            let mut carry = AB::Expr::ONE;
            for i in 0..T_BITS {
                let flip = l[i].clone() + carry.clone() - l[i].clone() * carry.clone().double();
                t.assert_zero(n[i].clone() - flip);
                carry *= l[i].clone();
            }
        }
        let bits = &l[0..T_BITS];
        let idx = (0..T_BITS).fold(AB::Expr::ZERO, |a, i| a + l[i].clone() * AB::Expr::from_u64(1 << i));
        let ce: Vec<[u64; 3]> = (0..ROWS).map(ctl_entry).collect();
        let msg = vec![
            idx.clone(),
            mle(bits, &ce.iter().map(|e| e[1]).collect::<Vec<_>>()),
            mle(bits, &ce.iter().map(|e| e[2]).collect::<Vec<_>>()),
        ];
        b.push_interaction(BUS_CTL, msg, -l[T_MC].clone(), 0);
        let ke: Vec<[u64; 7]> = (0..ROWS).map(k_entry).collect();
        let mut msg = vec![idx];
        for f in 1..7 {
            msg.push(mle(bits, &ke.iter().map(|e| e[f]).collect::<Vec<_>>()));
        }
        b.push_interaction(BUS_K, msg, -l[T_MK].clone(), 0);
    }
}

/// Test consumer of the interface bus: one row per (compression, word pair).
/// Columns: cid, pair index, 3 + 3 limbs, multiplicity.
#[derive(Clone, Copy, Debug)]
pub struct HarnessAir;
pub const H_WIDTH: usize = 9;
impl<F> BaseAir<F> for HarnessAir {
    fn width(&self) -> usize {
        H_WIDTH
    }
}
impl<F> PartitionedBaseAir<F> for HarnessAir {}
impl<F> BaseAirWithPublicValues<F> for HarnessAir {}
impl<AB: AirBuilderWithPublicValues + InteractionBuilder> Air<AB> for HarnessAir {
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        let l: Vec<AB::Expr> = main.row_slice(0).unwrap().iter().map(|&v| v.into()).collect();
        b.assert_bool(l[8].clone());
        b.push_interaction(BUS_IF, l[0..8].to_vec(), -l[8].clone(), 1);
    }
}
