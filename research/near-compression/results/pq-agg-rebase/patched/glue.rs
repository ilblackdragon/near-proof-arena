//! NV GLUE role: one row per *pair* of message words of a job compression (8 rows per
//! compression).  Replaces the packer (one row per word) and the block-chaining AIR
//! (one 102-column row per compression).
//!
//! Row q (0..8) of block k of a job holds
//! * the 16 big-endian bytes of block words 2q, 2q+1 (+ carry = next row's first byte),
//!   their air2 limb splits, and the framing (prefix, tag, felt / word units, 0x80
//!   padding, bit length) exactly as the v2 packer;
//! * one state pair `s` (6 limbs): for q < 4 the input pair q of this compression, which
//!   is also output pair q of the previous block's compression (cid - ROWS, compressions
//!   of a job are consecutive) or the IV for block 0; for q >= 4 in the last block the
//!   output pair q - 4 (digest pairs 0..2 are sent on the digest bus).
//!
//! The SHA compression AIR's 16 interface pairs per compression are received as: block
//! pair (cid, 4 + q) on every row, input pair (cid, q) on rows q < 4, output pair
//! (cid', 12 + q mod 4) on rows q < 4 of blocks > 0 (previous compression) and rows q >= 4
//! of the last block.
//!
//! The role is written against a column view so it can live in a shared AIR: every
//! constraint and interaction is gated by the role flag `kg` (`nkg` on the next row).
use core::borrow::{Borrow, BorrowMut};

use openvm_recursion_circuit_derive::AlignedBorrow;
use openvm_stark_backend::{
    interaction::{InteractionBuilder, LookupBus, PermutationCheckBus},
    BaseAirWithPublicValues, PartitionedBaseAir,
};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use super::{
    fmt::{limbs_from_bytes, split_bits, wl},
    hash::{cnt2, lookup_byte, lookup_pair, HashBuses, Job2, NODE_TAG, U2, UNIT_FELT, UNIT_HALF, UNIT_WORD},
};
use crate::sha384::{
    compress4_air::ROWS,
    compress4_trace::{Comp, SHA384_IV},
    config::{sha_levers, F},
};

#[repr(C)]
#[derive(AlignedBorrow, Debug)]
pub struct GlueCols<T> {
    /// first row of a job
    pub start: T,
    pub job: T,
    /// pair index bits (q = q0 + 2 q1 + 4 q2)
    pub q: [T; 3],
    /// compression id (index * ROWS)
    pub cid: T,
    pub blk0: T,
    pub last: T,
    /// = last * [q = 7] (last row of the job)
    pub end: T,
    /// = 1 - [header row] - [length row]
    pub act: T,
    /// padding started before this row
    pub phase: T,
    /// unit index before this row
    pub uidx: T,
    pub b: [T; 16],
    pub carry: T,
    /// low parts of b5, b2 (word 0) and b13, b10 (word 1)
    pub lo: [T; 4],
    /// word-unit views (b1..b8), (b9..b15, carry): low parts of their bytes 5 and 2
    pub ulo: [T; 4],
    /// padding-start flag per felt slot (A0 = b1..b4, B0 = b5..b8, A1 = b9..b12, B1 = b13..carry)
    pub p: [T; 4],
    /// word unit over slots (A0, B0) / (A1, B1)
    pub wd: [T; 2],
    /// felt slot is p - 1 (top byte 0x78)
    pub zm: [T; 4],
    /// state pair limbs
    pub s: [T; 6],
    /// Merkle-node job (one block: NODE_WORD || L || R, aligned word units)
    pub nd: T,
    /// next row's second byte (42-byte digests: shift-2 word units in node jobs)
    pub carry2: T,
    /// low 6 bits of limb 2 of output word 5 (truncated away in 42-byte digests)
    pub lo6: T,
    /// Merkle job (leaf / coset leaf / node): output digest truncated to 42 bytes
    pub tr: T,
    /// slot 2 holds a 2-byte digest tail followed by the 0x80 padding (42-byte digests)
    pub hp: T,
    /// a tail slot occurred before this row (bit length correction)
    pub hs: T,
    /// transcript blocks: this digest row's first / second word is read by the sample role
    /// (sent once more on the digest bus under key 8 + word index)
    pub dx: [T; 2],
}
pub const GLUE_W: usize = GlueCols::<u8>::width();

fn iv_pair(q: usize) -> [u32; 6] {
    let (a, b) = (wl(SHA384_IV[2 * q]), wl(SHA384_IV[2 * q + 1]));
    [a[0], a[1], a[2], b[0], b[1], b[2]]
}

/// GLUE constraints and interactions, gated by `kg` (role flag of the local row) and
/// `nkg` (of the next row).
pub fn eval_glue<AB: AirBuilder + InteractionBuilder>(
    builder: &mut AB,
    l: &GlueCols<AB::Var>,
    n: &GlueCols<AB::Var>,
    kg: AB::Expr,
    nkg: AB::Expr,
    buses: &HashBuses,
) {
    let one = AB::Expr::ONE;
    let c = |v: u64| AB::Expr::from_u64(v);
    let bool_g = |b: &mut AB, x: AB::Var| b.assert_zero(kg.clone() * x * (x - AB::Expr::ONE));
    for x in [l.start, l.blk0, l.last, l.end, l.nd, l.tr, l.hp, l.hs]
        .into_iter()
        .chain(l.q)
        .chain(l.p)
        .chain(l.wd)
        .chain(l.zm)
    {
        bool_g(builder, x);
    }
    let (q0, q1, q2) = (l.q[0], l.q[1], l.q[2]);
    let nq = |v: usize| -> [AB::Expr; 3] {
        core::array::from_fn(|i| {
            if (v >> i) & 1 == 1 {
                l.q[i].into()
            } else {
                one.clone() - l.q[i]
            }
        })
    };
    let is_q = |v: usize| -> AB::Expr {
        let [a, b, d] = nq(v);
        a * b * d
    };
    let q7: AB::Expr = q0 * q1 * q2;
    builder.assert_zero(kg.clone() * (l.end - l.last * q7.clone()));
    let hdr = l.blk0 * (one.clone() - q1) * (one.clone() - q2);
    let pj = one.clone() - l.nd; // prefix-framed job
    builder.assert_zero(kg.clone() * (l.act - pj.clone() * (one.clone() - hdr - l.end)));
    builder.assert_zero(kg.clone() * l.nd * (one.clone() - l.blk0));
    builder.assert_zero(kg.clone() * l.nd * (one.clone() - l.last));
    {
        let mut w = builder.when(kg.clone() * l.start);
        for i in 0..3 {
            w.assert_zero(l.q[i]);
        }
        w.assert_one(l.blk0);
        w.assert_zero(l.phase);
        w.assert_zero(l.uidx);
        w.assert_zero(l.hs);
    }
    let w42 = sha_levers().digest_bytes == 42;
    if !w42 {
        builder.assert_zero(kg.clone() * l.hp);
    }

    // ---- felt / word unit slots ----
    let b: [AB::Expr; 16] = l.b.map(Into::into);
    let slots: [[AB::Expr; 4]; 4] = [
        [b[1].clone(), b[2].clone(), b[3].clone(), b[4].clone()],
        [b[5].clone(), b[6].clone(), b[7].clone(), b[8].clone()],
        [b[9].clone(), b[10].clone(), b[11].clone(), b[12].clone()],
        [b[13].clone(), b[14].clone(), b[15].clone(), l.carry.into()],
    ];
    let units: [[AB::Expr; 8]; 2] = [
        core::array::from_fn(|k| b[1 + k].clone()),
        core::array::from_fn(|k| if k < 7 { b[9 + k].clone() } else { l.carry.into() }),
    ];
    let ul: [[AB::Expr; 3]; 2] = [
        limbs_from_bytes(&units[0], l.ulo[0].into(), l.ulo[1].into()),
        limbs_from_bytes(&units[1], l.ulo[2].into(), l.ulo[3].into()),
    ];
    let slot = PermutationCheckBus::new(buses.slot);
    let act: AB::Expr = l.act.into();
    let mut phb: AB::Expr = l.phase.into();
    let mut uidx: AB::Expr = l.uidx.into();
    let mut d: Vec<AB::Expr> = vec![];
    // 2-byte tail view (bytes 0, 1 of slot 2 = b9, b10), as a word with zero low bytes
    let tail = limbs_from_bytes(
        &[b[9].clone(), b[10].clone(), AB::Expr::ZERO, AB::Expr::ZERO, AB::Expr::ZERO, AB::Expr::ZERO, AB::Expr::ZERO, AB::Expr::ZERO],
        AB::Expr::ZERO,
        AB::Expr::ZERO,
    );
    for s in 0..4 {
        let p = l.p[s];
        let hps: AB::Expr = if s == 2 { l.hp.into() } else { AB::Expr::ZERO };
        let ds = act.clone() * (one.clone() - phb.clone()) - p - hps.clone();
        if s == 2 {
            builder.assert_zero(kg.clone() * l.hp * phb.clone());
            builder.assert_zero(kg.clone() * l.hp * (one.clone() - act.clone()));
            builder.assert_zero(kg.clone() * l.hp * l.wd[1]);
            builder.assert_zero(kg.clone() * l.hp * (slots[2][2].clone() - c(0x80)));
            builder.assert_zero(kg.clone() * l.hp * slots[2][3].clone());
        }
        builder.assert_zero(kg.clone() * p * phb.clone());
        builder.assert_zero(kg.clone() * p * (one.clone() - act.clone()));
        let a = &slots[s];
        // padding slot: 0x80 0 0 0; empty slot (after padding): zeros
        builder.assert_zero(kg.clone() * p * (a[0].clone() - c(0x80)));
        for k in 1..4 {
            builder.assert_zero(kg.clone() * p * a[k].clone());
        }
        for k in 0..4 {
            builder.assert_zero(kg.clone() * act.clone() * phb.clone() * a[k].clone());
        }
        let w = s / 2;
        let is_felt = ds.clone() - l.wd[w];
        let felt = a[0].clone() + a[1].clone() * c(1 << 8) + a[2].clone() * c(1 << 16) + a[3].clone() * c(1 << 24);
        // canonical felt: top byte <= 0x78, and == 0x78 only for p - 1 = 0x78000000
        let gap = c(0x78) - a[3].clone();
        lookup_byte(builder, buses.byte, gap.clone() - one.clone() + l.zm[s], kg.clone() * is_felt.clone());
        builder.assert_zero(kg.clone() * l.zm[s] * gap);
        builder.assert_zero(kg.clone() * l.zm[s] * (a[0].clone() + a[1].clone() + a[2].clone()));
        if s % 2 == 0 {
            let wdv: AB::Expr = l.wd[w].into();
            let wordish = wdv.clone() + hps.clone();
            let [u0, u1, u2] = ul[w].clone();
            let [t0, t1, t2] = tail.clone();
            slot.receive(
                builder,
                [
                    one.clone(),
                    l.job.into(),
                    uidx.clone(),
                    // a 42-B digest tail has its own kind (UNIT_HALF), so a tail unit cannot be
                    // framed as a full word and a word cannot be framed as a tail
                    wdv.clone() * c(UNIT_WORD as u64)
                        + hps.clone() * c(UNIT_HALF as u64)
                        + (one.clone() - wordish.clone()) * c(UNIT_FELT as u64),
                    (one.clone() - wordish) * felt + wdv.clone() * u0 + hps.clone() * t0,
                    wdv.clone() * u1 + hps.clone() * t1,
                    wdv * u2 + hps.clone() * t2,
                ],
                kg.clone() * (ds.clone() + hps.clone()),
            );
        } else {
            slot.receive(
                builder,
                [
                    one.clone(),
                    l.job.into(),
                    uidx.clone(),
                    c(UNIT_FELT as u64),
                    felt,
                    AB::Expr::ZERO,
                    AB::Expr::ZERO,
                ],
                kg.clone() * is_felt,
            );
        }
        phb = phb + p + hps.clone();
        uidx = uidx + ds.clone() + hps.double();
        d.push(ds);
    }
    for w in 0..2 {
        builder.assert_zero(kg.clone() * l.wd[w] * (one.clone() - d[2 * w].clone()));
        builder.assert_zero(kg.clone() * l.wd[w] * (one.clone() - d[2 * w + 1].clone()));
    }
    let (phase_after, uidx_after) = (phb, uidx);

    // ---- framing ----
    let q_0 = is_q(0);
    let q_1 = is_q(1);
    let kp = kg.clone() * pj.clone();
    let prefix = sha_levers().prefix();
    for k in 0..16 {
        builder.assert_zero(kp.clone() * l.blk0 * q_0.clone() * (l.b[k] - c(prefix[k] as u64)));
        builder.assert_zero(kp.clone() * l.blk0 * q_1.clone() * (l.b[k] - c(prefix[16 + k] as u64)));
    }
    for k in 0..13 {
        builder.assert_zero(kp.clone() * l.end * l.b[k]);
    }
    builder.assert_zero(
        kp.clone()
            * l.end
            * (l.b[13] * c(1 << 16) + l.b[14] * c(1 << 8) + l.b[15] - (c(33) + l.uidx * c(4) - l.hs * c(6)) * c(8)),
    );
    // padding must have started by word 13 exactly in the last block
    builder.assert_zero(kp.clone() * is_q(6) * (l.last - phase_after.clone()));
    // tag: first byte of word 4 (row 2 of block 0); node jobs: NODE_TAG at row 0
    PermutationCheckBus::new(buses.job).receive(
        builder,
        [l.job.into(), pj.clone() * b[0].clone() + l.nd * c(NODE_TAG as u64), l.tr.into()],
        kg.clone() * l.blk0 * (pj.clone() * is_q(2) + l.nd * q_0.clone()),
    );
    // node jobs: constant words 0 (node prefix), padding and bit length
    let kn = kg.clone() * l.nd;
    let node_w = sha_levers().node_prefix();
    for k in 0..8 {
        builder.assert_zero(kn.clone() * q_0.clone() * (l.b[k] - c(node_w[k] as u64)));
    }
    if !w42 {
        // 48 B: words 13 (0x80 pad), 14 (0), 15 (832)
        let pad_w = (0x80u64 << 56).to_be_bytes();
        let len_w = [0u64.to_be_bytes(), 832u64.to_be_bytes()].concat();
        for k in 0..8 {
            builder.assert_zero(kn.clone() * is_q(6) * (l.b[8 + k] - c(pad_w[k] as u64)));
        }
        for k in 0..16 {
            builder.assert_zero(kn.clone() * q7.clone() * (l.b[k] - c(len_w[k] as u64)));
        }
    } else {
        // 42 B: message 8 + 84 = 92 bytes: byte 92 (row 5, b12) = 0x80, then zeros, length 736
        builder.assert_zero(kn.clone() * is_q(5) * (l.b[12] - c(0x80)));
        for k in 13..16 {
            builder.assert_zero(kn.clone() * is_q(5) * l.b[k]);
        }
        for k in 0..16 {
            builder.assert_zero(kn.clone() * is_q(6) * l.b[k]);
        }
        let len_w = [0u64.to_be_bytes(), 736u64.to_be_bytes()].concat();
        for k in 0..16 {
            builder.assert_zero(kn.clone() * q7.clone() * (l.b[k] - c(len_w[k] as u64)));
        }
    }
    // Merkle-job flag tr: declared by the job's producer on the job bus (ALU leaf / node jobs: 1,
    // hash-chain transcript jobs: 0)

    // ---- sequencing ----
    {
        let mut t = builder.when_transition();
        let cont = kg.clone() * nkg.clone() * (one.clone() - l.end);
        let qv = |x: &GlueCols<AB::Var>| x.q[0] + x.q[1] * c(2) + x.q[2] * c(4);
        t.assert_zero(cont.clone() * (n.job - l.job));
        t.assert_zero(cont.clone() * (qv(n) - qv(l) - one.clone() + q7.clone() * c(8)));
        t.assert_zero(cont.clone() * (n.blk0 - l.blk0 * (one.clone() - q7.clone())));
        t.assert_zero(cont.clone() * (n.cid - l.cid - q7.clone() * c(ROWS as u64)));
        t.assert_zero(cont.clone() * (n.phase - phase_after));
        t.assert_zero(cont.clone() * (n.uidx - uidx_after));
        t.assert_zero(cont.clone() * (n.b[0] - l.carry));
        t.assert_zero(cont.clone() * (one.clone() - q7.clone()) * (n.last - l.last));
        t.assert_zero(cont.clone() * n.start);
        t.assert_zero(cont.clone() * (n.nd - l.nd));
        t.assert_zero(cont.clone() * (n.tr - l.tr));
        t.assert_zero(cont.clone() * (n.hs - l.hs - l.hp));
        t.assert_zero(cont.clone() * (n.b[1] - l.carry2));
        t.assert_zero(kg.clone() * nkg.clone() * l.end * (one.clone() - n.start));
        t.assert_zero(kg.clone() * (one.clone() - nkg.clone()) * (one.clone() - l.end));
        t.assert_zero(nkg.clone() * (one.clone() - kg.clone()) * (one.clone() - n.start));
    }
    builder.when_first_row().assert_zero(kg.clone() * (one.clone() - l.start));
    builder.when_last_row().assert_zero(kg.clone() * (one.clone() - l.end));

    // ---- state pairs and SHA interface ----
    let s: Vec<AB::Expr> = l.s.iter().map(|&x| x.into()).collect();
    for i in 0..6 {
        let mut ivp = AB::Expr::ZERO;
        for v in 0..4 {
            let sel = (if v & 1 == 1 { q0.into() } else { one.clone() - q0 })
                * (if v & 2 == 2 { q1.into() } else { one.clone() - q1 });
            ivp += sel * c(iv_pair(v)[i] as u64);
        }
        builder.assert_zero(kg.clone() * l.blk0 * (one.clone() - q2) * (l.s[i] - ivp));
    }
    let (a5, a2) = split_bits();
    let w0b: [AB::Expr; 8] = core::array::from_fn(|k| b[k].clone());
    let w1b: [AB::Expr; 8] = core::array::from_fn(|k| b[8 + k].clone());
    let w0 = limbs_from_bytes(&w0b, l.lo[0].into(), l.lo[1].into());
    let w1 = limbs_from_bytes(&w1b, l.lo[2].into(), l.lo[3].into());
    let qv = q0 + q1 * c(2) + q2 * c(4);
    if !w42 {
        // node jobs: word 2q (q in 1..=6) is unit 4q - 2, word 2q + 1 (q in 0..=5) is unit 4q
        for (limbs, idx, mult) in [
            (w0.clone(), qv.clone() * c(4) - c(2), one.clone() - q_0.clone() - q7.clone()),
            (w1.clone(), qv.clone() * c(4), one.clone() - is_q(6) - q7.clone()),
        ] {
            let [l0, l1, l2] = limbs;
            slot.receive(
                builder,
                [one.clone(), l.job.into(), idx, c(UNIT_WORD as u64), l0, l1, l2],
                kn.clone() * mult,
            );
        }
    } else {
        // 42 B node: L0..L4 aligned (words 1..5), L5 tail = bytes 0,1 of word 6, R words at
        // byte offset 50 (shift 2), R5 tail = bytes 2,3 of word 11.
        let zero = || AB::Expr::ZERO;
        let virt = |x0: AB::Expr, x1: AB::Expr| {
            limbs_from_bytes(&[x0, x1, zero(), zero(), zero(), zero(), zero(), zero()], zero(), zero())
        };
        let s2: [AB::Expr; 8] = core::array::from_fn(|k| b[2 + k].clone());
        let s3: [AB::Expr; 8] = core::array::from_fn(|k| match k {
            0..=5 => b[10 + k].clone(),
            6 => l.carry.into(),
            _ => l.carry2.into(),
        });
        let s2l = limbs_from_bytes(&s2, l.ulo[0].into(), l.ulo[1].into());
        let s3l = limbs_from_bytes(&s3, l.ulo[2].into(), l.ulo[3].into());
        let l5 = virt(b[0].clone(), b[1].clone());
        let r5 = virt(b[10].clone(), b[11].clone());
        let (q_2, q_3, q_4, q_5) = (is_q(2), is_q(3), is_q(4), is_q(5));
        let mix = |parts: &[(AB::Expr, &[AB::Expr; 3])]| -> [AB::Expr; 3] {
            core::array::from_fn(|t| parts.iter().fold(AB::Expr::ZERO, |acc, (sel, l)| acc + sel.clone() * l[t].clone()))
        };
        // unit 1: q0 w1 (0), q1 w0 (2), q2 w0 (6), q3 L5 tail (10)
        let u1 = mix(&[(q_0.clone(), &w1), (q_1.clone(), &w0), (q_2.clone(), &w0), (q_3.clone(), &l5)]);
        let i1 = q_1.clone() * c(2) + q_2.clone() * c(6) + q_3.clone() * c(10);
        let m1 = q_0.clone() + q_1.clone() + q_2.clone() + q_3.clone();
        // unit 2: q1 w1 (4), q2 w1 (8), q3 R0 (12), q4 R2 (16), q5 R4 (20)
        let u2 = mix(&[(q_1.clone(), &w1), (q_2.clone(), &w1), (q_3.clone() + q_4.clone() + q_5.clone(), &s2l)]);
        let i2 = q_1.clone() * c(4) + q_2.clone() * c(8) + q_3.clone() * c(12) + q_4.clone() * c(16) + q_5.clone() * c(20);
        let m2 = q_1.clone() + q_2.clone() + q_3.clone() + q_4.clone() + q_5.clone();
        // unit 3: q3 R1 (14), q4 R3 (18), q5 R5 tail (22)
        let u3 = mix(&[(q_3.clone() + q_4.clone(), &s3l), (q_5.clone(), &r5)]);
        let i3 = q_3.clone() * c(14) + q_4.clone() * c(18) + q_5.clone() * c(22);
        let m3 = q_3 + q_4 + q_5;
        for (limbs, idx, mult) in [(u1, i1, m1), (u2, i2, m2), (u3, i3, m3)] {
            let [l0, l1, l2] = limbs;
            slot.receive(
                builder,
                [one.clone(), l.job.into(), idx, c(UNIT_WORD as u64), l0, l1, l2],
                kn.clone() * mult,
            );
        }
    }
    let iface = PermutationCheckBus::new(buses.iface);
    let mut msg = vec![l.cid.into(), qv.clone() + c(4)];
    msg.extend(w0.into_iter().chain(w1));
    iface.receive(builder, msg, kg.clone());
    let mut msg = vec![l.cid.into(), qv];
    msg.extend(s.iter().cloned());
    iface.receive(builder, msg, kg.clone() * (one.clone() - q2));
    let mut msg = vec![
        l.cid - (one.clone() - q2) * c(ROWS as u64),
        c(12) + q0 + q1 * c(2),
    ];
    msg.extend(s.iter().cloned());
    iface.receive(
        builder,
        msg,
        kg.clone() * ((one.clone() - q2) * (one.clone() - l.blk0) + q2 * l.last),
    );
    let mut msg = vec![l.job.into(), q0 + q1 * c(2)];
    if w42 {
        // Merkle jobs: word 5 truncated to its top 2 bytes (limbs (0, 0, l2 - lo6), lo6 < 64)
        let t6 = l.tr * is_q(6);
        let mut sv = s.clone();
        sv[3] = s[3].clone() * (one.clone() - t6.clone());
        sv[4] = s[4].clone() * (one.clone() - t6.clone());
        sv[5] = s[5].clone() - t6 * l.lo6;
        msg.extend(sv);
    } else {
        msg.extend(s.iter().cloned());
    }
    lookup_byte(builder, buses.byte, l.lo6 * c(4), kg.clone());
    let drow = l.last * q2.clone() * (one.clone() - q0.clone() * q1.clone());
    PermutationCheckBus::new(buses.digest).send(builder, msg, kg.clone() * drow.clone());
    // words read by the sample role: (job, 8 + word, 3 limbs, 0, 0, 0); only on digest rows of
    // untruncated (transcript) jobs; the multiplicity is pinned by the bus balance
    for h in 0..2 {
        builder.assert_zero(kg.clone() * l.dx[h] * (l.dx[h] - one.clone()));
        builder.assert_zero(kg.clone() * l.dx[h] * (one.clone() - drow.clone()));
        builder.assert_zero(kg.clone() * l.dx[h] * l.tr);
        let widx = (q0.clone() + q1.clone() * c(2)) * c(2) + c(8 + h as u64);
        PermutationCheckBus::new(buses.digest).send(
            builder,
            [l.job.into(), widx, s[3 * h].clone(), s[3 * h + 1].clone(), s[3 * h + 2].clone(), AB::Expr::ZERO, AB::Expr::ZERO, AB::Expr::ZERO],
            kg.clone() * l.dx[h],
        );
    }

    // ---- byte range checks ----
    for k in 0..8 {
        lookup_pair(builder, buses.byte, l.b[2 * k], l.b[2 * k + 1], kg.clone());
    }
    for (x, y) in [(l.lo[0], l.lo[1]), (l.lo[2], l.lo[3]), (l.ulo[0], l.ulo[1]), (l.ulo[2], l.ulo[3])] {
        lookup_pair(builder, buses.byte, x * c(1 << (8 - a5)), y * c(1 << (8 - a2)), kg.clone());
    }
}

/// Standalone GLUE AIR: column 0 = role flag, then the GLUE view.
#[derive(Clone, Copy, Debug)]
pub struct GlueAir {
    pub buses: HashBuses,
}
impl<T> BaseAir<T> for GlueAir {
    fn width(&self) -> usize {
        1 + GLUE_W
    }
}
impl<T> BaseAirWithPublicValues<T> for GlueAir {}
impl<T> PartitionedBaseAir<T> for GlueAir {}
impl<AB: AirBuilder + InteractionBuilder> Air<AB> for GlueAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let (local, next) = (main.row_slice(0).unwrap(), main.row_slice(1).unwrap());
        let (kg, nkg) = (local[0], next[0]);
        builder.assert_bool(kg);
        let l: &GlueCols<AB::Var> = local[1..].borrow();
        let n: &GlueCols<AB::Var> = next[1..].borrow();
        eval_glue(builder, l, n, kg.into(), nkg.into(), &self.buses);
    }
}

fn split_lo(byte: u8, a: usize) -> u8 {
    byte & ((1 << a) - 1)
}

/// GLUE rows for the jobs (compressions numbered from `cid_base`, in job order).
/// Returns the rows (each GLUE_W wide) and adds byte-table counts.
pub fn glue_rows(jobs: &[Job2], job_blocks: &[(Vec<Comp>, [u64; 6])], cid_base: usize, counts: &mut [u32]) -> Vec<[F; GLUE_W]> {
    let (a5, a2) = split_bits();
    let mut rows = vec![];
    let mut comp = cid_base;
    for (job, j) in jobs.iter().enumerate() {
        let m = j.message();
        let blocks = &job_blocks[job].0;
        let nb = blocks.len();
        let padded: Vec<u8> = blocks.iter().flat_map(|c| c.block.iter().flat_map(|w| w.to_be_bytes())).collect();
        debug_assert_eq!(&padded[..m.len()], &m[..]);
        let mut slots: Vec<U2> = vec![];
        for u in &j.units {
            assert!(matches!(u, U2::Felt(_)) || slots.len() % 2 == 0, "word units must start at an even unit index");
            for _ in 0..u.nunits() {
                slots.push(*u);
            }
        }
        let total = slots.len();
        let (mut phase, mut uidx) = (false, 0usize);
        let w42 = sha_levers().digest_bytes == 42;
        // ALU-started jobs are truncated (job bus tr = 1): leaves, coset leaves,
        // [agg] range statements (tag 9), statements
        let merkle = j.node
            || j.tag == 0
            || j.tag == crate::sha384::config::TAG_COSET_LEAF
            || j.tag == crate::sha384::config::TAG_RANGE
            || j.tag == crate::sha384::config::TAG_STATEMENT;
        let trunc = w42 && merkle;
        let mut hs = false;
        if j.node {
            assert_eq!(nb, 1);
            uidx = total;
        }
        for (k, cb) in blocks.iter().enumerate() {
            let last = k + 1 == nb;
            let out = crate::sha384::compress2_trace::sha2_compress(cb);
            for q in 0..8 {
                let mut r = [F::ZERO; GLUE_W];
                let g: &mut GlueCols<F> = r.as_mut_slice().borrow_mut();
                g.start = F::from_bool(k == 0 && q == 0);
                g.job = F::from_u32(j.id);
                for i in 0..3 {
                    g.q[i] = F::from_bool((q >> i) & 1 == 1);
                }
                g.cid = F::from_usize(comp * ROWS);
                g.blk0 = F::from_bool(k == 0);
                g.last = F::from_bool(last);
                if last && (4..7).contains(&q) {
                    for h in 0..2 {
                        g.dx[h] = F::from_bool((j.wread >> (2 * (q - 4) + h)) & 1 == 1);
                    }
                }
                g.end = F::from_bool(last && q == 7);
                let hdr = k == 0 && q < 2;
                let lenw = last && q == 7;
                g.nd = F::from_bool(j.node);
                g.act = F::from_bool(!(hdr || lenw || j.node));
                g.phase = F::from_bool(phase && !j.node);
                g.uidx = F::from_usize(if j.node { 0 } else { uidx });
                g.tr = F::from_bool(merkle);
                g.hs = F::from_bool(hs);
                let off = 128 * k + 16 * q;
                let bytes = &padded[off..off + 16];
                for t in 0..16 {
                    g.b[t] = F::from_u8(bytes[t]);
                }
                for t in 0..8 {
                    cnt2(counts, bytes[2 * t] as usize, bytes[2 * t + 1] as usize);
                }
                let carry = if off + 16 < padded.len() { padded[off + 16] } else { 0 };
                let carry2 = if off + 17 < padded.len() { padded[off + 17] } else { 0 };
                g.carry = F::from_u8(carry);
                g.carry2 = F::from_u8(carry2);
                let los = [split_lo(bytes[5], a5), split_lo(bytes[2], a2), split_lo(bytes[13], a5), split_lo(bytes[10], a2)];
                let mut ulos = [0u8; 4];
                let sb: [[u8; 4]; 4] = [
                    [bytes[1], bytes[2], bytes[3], bytes[4]],
                    [bytes[5], bytes[6], bytes[7], bytes[8]],
                    [bytes[9], bytes[10], bytes[11], bytes[12]],
                    [bytes[13], bytes[14], bytes[15], carry],
                ];
                if !(hdr || lenw || j.node) {
                    let mut s = 0;
                    while s < 4 {
                        let w = s / 2;
                        if !phase && uidx < total {
                            if let U2::Half(_) = slots[uidx] {
                                assert_eq!(s, 2, "digest tail must sit in slot 2");
                                debug_assert_eq!(&sb[2][2..], &[0x80, 0]);
                                g.hp = F::ONE;
                                hs = true;
                                uidx += 2;
                                phase = true;
                                s += 1;
                                continue;
                            }
                            if let U2::Word(wv) = slots[uidx] {
                                assert_eq!(s % 2, 0, "word unit must start at a word slot");
                                let ub: Vec<u8> = sb[s].iter().chain(sb[s + 1].iter()).copied().collect();
                                debug_assert_eq!(wv.to_be_bytes().to_vec(), ub);
                                g.wd[w] = F::ONE;
                                ulos[2 * w] = split_lo(ub[5], a5);
                                ulos[2 * w + 1] = split_lo(ub[2], a2);
                                uidx += 2;
                                s += 2;
                                continue;
                            }
                            let a = sb[s];
                            let gap = 0x78i64 - a[3] as i64;
                            assert!(gap >= 0, "non-canonical felt unit");
                            let zm = gap == 0;
                            g.zm[s] = F::from_bool(zm);
                            cnt2(counts, (gap - 1 + zm as i64) as usize, 0);
                            uidx += 1;
                        } else if !phase {
                            debug_assert_eq!(sb[s], [0x80, 0, 0, 0]);
                            g.p[s] = F::ONE;
                            phase = true;
                        }
                        s += 1;
                    }
                }
                if j.node && w42 && (3..=5).contains(&q) {
                    // shift-2 views (b2..b9), (b10..b15, carry, carry2): splits of their bytes 5, 2
                    ulos = [split_lo(bytes[7], a5), split_lo(bytes[4], a2), split_lo(bytes[15], a5), split_lo(bytes[12], a2)];
                }
                if trunc && last && q == 6 {
                    g.lo6 = F::from_u32(wl(out[5])[2] & 63);
                }
                cnt2(counts, (p3_field::PrimeField32::as_canonical_u32(&g.lo6) * 4) as usize, 0);
                for t in 0..4 {
                    g.lo[t] = F::from_u8(los[t]);
                    g.ulo[t] = F::from_u8(ulos[t]);
                }
                for v in [los, ulos] {
                    cnt2(counts, (v[0] as usize) << (8 - a5), (v[1] as usize) << (8 - a2));
                    cnt2(counts, (v[2] as usize) << (8 - a5), (v[3] as usize) << (8 - a2));
                }
                if q == 6 && !j.node {
                    assert_eq!(phase, last, "padding/final-block mismatch");
                }
                let pair = |w: [u64; 2]| -> [F; 6] {
                    let (a, b) = (wl(w[0]), wl(w[1]));
                    [a[0], a[1], a[2], b[0], b[1], b[2]].map(F::from_u32)
                };
                if q < 4 {
                    g.s = pair([cb.h[2 * q], cb.h[2 * q + 1]]);
                } else if last {
                    g.s = pair([out[2 * (q - 4)], out[2 * (q - 4) + 1]]);
                }
                rows.push(r);
            }
            comp += 1;
        }
        assert_eq!(uidx, total);
    }
    rows
}

/// Standalone GLUE matrix (role flag column + rows), padded to `h` rows.
pub fn glue_matrix(rows: &[[F; GLUE_W]], min_h: usize) -> RowMajorMatrix<F> {
    let h = rows.len().next_power_of_two().max(min_h).max(2);
    let mut v = F::zero_vec(h * (1 + GLUE_W));
    for (i, r) in rows.iter().enumerate() {
        v[i * (1 + GLUE_W)] = F::ONE;
        v[i * (1 + GLUE_W) + 1..(i + 1) * (1 + GLUE_W)].copy_from_slice(r);
    }
    RowMajorMatrix::new(v, 1 + GLUE_W)
}

#[allow(dead_code)]
fn _w(m: &RowMajorMatrix<F>) -> usize {
    m.width()
}
