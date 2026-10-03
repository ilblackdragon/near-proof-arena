//! NODE table: one row per revealed trie node (`RawTrieNodeWithSize`).
//!
//! The row holds the node's serialization in parsed form and emits it twice:
//! as the pre-state message `K_NPRE|N` and the post-state message
//! `K_NPOST|N`. The two differ only in 32-byte hash windows:
//!
//! * child window `j` of a branch (or the child of an extension, window 0):
//!   if the child is revealed (`rv[j]`, node id `cid[j]`) the pre window is
//!   the child's pre digest and the post window its post digest (both looked
//!   up on `BUS_DIGEST`); otherwise post = pre;
//! * the value hash of a leaf / branch-with-value: if the slot is touched
//!   (`tv`, account `vk`) the pre window is the digest of `K_VPRE|vk` and the
//!   post window that of `K_VPOST|vk`, and `len = 72`; otherwise post = pre.
//!
//! Node 0 is the root: its pre/post digests are the public pre-state root and
//! slice post root. Layouts (nearcore `raw_node.rs`, borsh):
//!
//! ```text
//! leaf   0 ‖ u32 hplen ‖ hp ‖ u32 vlen ‖ vhash ‖ u64 mem
//! b-1    1 ‖ u16 bitmap ‖ child hash × popcount ‖ u64 mem
//! b-2    2 ‖ u32 vlen ‖ vhash ‖ u16 bitmap ‖ child hash × popcount ‖ u64 mem
//! ext    3 ‖ u32 hplen ‖ hp ‖ child hash ‖ u64 mem
//! hp     = (0x20·leaf + 0x10·odd + x0) ‖ (hi‖lo nibble pairs)
//! ```
//!
//! Walk edges (`BUS_EDGE`) are provided from the parsed key nibbles and the
//! revealed children; an extension's end state jumps to its child on
//! `BUS_EPS`; a touched value slot is offered once on `BUS_VSLOT` at the
//! terminal state `(N, s)` (leaf with `s` nibbles) or `(N, 0)` (branch).
//! The running sum `S` of revealed bytes (node bytes + 72 per touched value)
//! is bounded by 3,000,000 (`witness_size`).

use super::*;
use crate::consts::*;

pub struct NodeCols {
    pub act: usize,
    pub isf: usize,
    pub lastn: usize,
    pub nid: usize,
    pub tl: usize,
    pub te: usize,
    pub tb1: usize,
    pub tb2: usize,
    pub odd: usize,
    pub x0: usize,
    pub kb: Vec<usize>,
    pub khi: Vec<usize>,
    pub klo: Vec<usize>,
    pub vlen: Vec<usize>,
    pub vh: Vec<usize>,
    pub pvh: Vec<usize>,
    pub tv: usize,
    pub vk: usize,
    pub bm: Vec<usize>,
    pub w: Vec<Vec<usize>>,
    pub pw: Vec<Vec<usize>>,
    pub rv: Vec<usize>,
    pub cid: Vec<usize>,
    pub me: Vec<usize>,
    pub mem: Vec<usize>,
    pub m_nib: usize,
    pub m_eps: usize,
    pub pv_: usize,
    pub pc: usize,
    pub pm: usize,
    pub s: usize,
    pub ssum: usize,
    pub wsd: Vec<usize>,
    pub width: usize,
}

impl NodeCols {
    pub fn new() -> Self {
        let mut a = Alloc::default();
        let mut c = NodeCols {
            act: a.one(),
            isf: a.one(),
            lastn: a.one(),
            nid: a.one(),
            tl: a.one(),
            te: a.one(),
            tb1: a.one(),
            tb2: a.one(),
            odd: a.one(),
            x0: a.one(),
            kb: a.vec(MAX_KEY_BYTES),
            khi: a.vec(MAX_KEY_BYTES),
            klo: a.vec(MAX_KEY_BYTES),
            vlen: a.vec(4),
            vh: a.vec(32),
            pvh: a.vec(32),
            tv: a.one(),
            vk: a.one(),
            bm: a.vec(16),
            w: (0..16).map(|_| a.vec(32)).collect(),
            pw: (0..16).map(|_| a.vec(32)).collect(),
            rv: a.vec(16),
            cid: a.vec(16),
            me: a.vec(16),
            mem: a.vec(8),
            m_nib: a.one(),
            m_eps: a.one(),
            pv_: a.one(),
            pc: a.one(),
            pm: a.one(),
            s: a.one(),
            ssum: a.one(),
            wsd: a.vec(3),
            width: 0,
        };
        c.width = a.0;
        c
    }
}

#[derive(Clone)]
pub struct NodeAir {
    pub c: std::sync::Arc<NodeCols>,
}

impl NodeAir {
    pub fn new() -> Self {
        NodeAir { c: std::sync::Arc::new(NodeCols::new()) }
    }
    pub fn width(&self) -> usize {
        self.c.width
    }
    pub fn eval<AB: AirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        let c = &*self.c;
        let r = Rows::<AB>::new(b, true);
        let pvs: Vec<AB::Expr> = (0..NUM_PV).map(|i| pv::<AB>(b, i)).collect();
        let v = |i: usize| r.c(i);
        let vs = |ix: &[usize]| -> Vec<AB::Expr> { ix.iter().map(|&i| r.c(i)).collect() };
        let one = AB::Expr::ONE;
        let (act, isf, lastn) = (v(c.act), v(c.isf), v(c.lastn));
        let (tl, te, tb1, tb2) = (v(c.tl), v(c.te), v(c.tb1), v(c.tb2));
        let (odd, tv) = (v(c.odd), v(c.tv));
        for x in [&act, &isf, &lastn, &tl, &te, &tb1, &tb2, &odd, &tv] {
            b.assert_bool(x.clone());
        }
        b.assert_eq(tl.clone() + te.clone() + tb1.clone() + tb2.clone(), act.clone());
        let le = tl.clone() + te.clone();
        let br = tb1.clone() + tb2.clone();
        b.when_first_row().assert_one(isf.clone());
        b.when_first_row().assert_one(act.clone());
        b.when_first_row().assert_zero(v(c.nid));
        b.when_last_row().assert_eq(lastn.clone(), act.clone());

        // ---- key (leaf / extension) ----------------------------------------
        let kb = vs(&c.kb);
        let khi = vs(&c.khi);
        let klo = vs(&c.klo);
        for m in 0..MAX_KEY_BYTES {
            b.assert_bool(kb[m].clone());
            if m + 1 < MAX_KEY_BYTES {
                b.assert_zero(kb[m + 1].clone() * (one.clone() - kb[m].clone()));
            }
            b.assert_zero((one.clone() - kb[m].clone()) * khi[m].clone());
            b.assert_zero((one.clone() - kb[m].clone()) * klo[m].clone());
        }
        b.assert_zero((one.clone() - le.clone()) * kb[0].clone());
        b.assert_zero((one.clone() - le.clone()) * odd.clone());
        b.assert_zero((one.clone() - odd.clone()) * v(c.x0));
        let nkb = kb.iter().fold(AB::Expr::ZERO, |a, x| a + x.clone());
        let hplen = one.clone() + nkb.clone();
        let s = nkb * AB::Expr::TWO + odd.clone();
        b.assert_eq(v(c.s), s.clone());
        let s = v(c.s);

        // ---- bitmap / children ----------------------------------------------------
        let bm = vs(&c.bm);
        let mut pop = AB::Expr::ZERO;
        let mut pcs = Vec::with_capacity(16);
        for j in 0..16 {
            b.assert_bool(bm[j].clone());
            b.assert_zero((one.clone() - br.clone()) * bm[j].clone());
            pcs.push(pop.clone());
            pop = pop + bm[j].clone();
        }
        let slot_act: Vec<AB::Expr> = (0..16)
            .map(|j| br.clone() * bm[j].clone() + if j == 0 { te.clone() } else { AB::Expr::ZERO })
            .collect();
        for j in 0..16 {
            let rv = v(c.rv[j]);
            b.assert_bool(rv.clone());
            b.assert_zero(rv.clone() * (one.clone() - slot_act[j].clone()));
            for i in 0..32 {
                b.assert_zero((one.clone() - rv.clone()) * (v(c.pw[j][i]) - v(c.w[j][i])));
            }
            b.assert_zero((one.clone() - br.clone() * rv.clone()) * v(c.me[j]));
        }
        b.assert_zero((one.clone() - te.clone() * v(c.rv[0])) * v(c.m_eps));
        b.assert_zero((one.clone() - le.clone()) * v(c.m_nib));

        // ---- value slot -----------------------------------------------------------
        let gv = tl.clone() + tb2.clone();
        b.assert_zero(tv.clone() * (one.clone() - gv.clone()));
        b.assert_zero(tv.clone() * (v(c.vlen[0]) - k::<AB>(72)));
        for i in 1..4 {
            b.assert_zero(tv.clone() * v(c.vlen[i]));
        }
        for i in 0..32 {
            b.assert_zero((one.clone() - tv.clone()) * (v(c.pvh[i]) - v(c.vh[i])));
        }

        // ---- positions ----------------------------------------------------------------
        let five_hp = k::<AB>(5) + hplen.clone();
        b.assert_eq(v(c.pv_), tl.clone() * five_hp.clone() + tb2.clone());
        b.assert_eq(
            v(c.pc),
            te.clone() * five_hp.clone() + tb1.clone() * k::<AB>(3) + tb2.clone() * k::<AB>(39),
        );
        b.assert_eq(
            v(c.pm),
            tl.clone() * (five_hp.clone() + k::<AB>(36))
                + te.clone() * (five_hp.clone() + k::<AB>(32))
                + tb1.clone() * (k::<AB>(3) + pop.clone() * k::<AB>(32))
                + tb2.clone() * (k::<AB>(39) + pop.clone() * k::<AB>(32)),
        );
        let msg_len = v(c.pm) + k::<AB>(8);

        // ---- row structure, running witness size -------------------------------------
        b.when_first_row().assert_eq(v(c.ssum), msg_len.clone() + tv.clone() * k::<AB>(72));
        {
            let (nact, nid, nisf) = (r.n(c.act), r.n(c.nid), r.n(c.isf));
            let n_len = r.n(c.pm) + k::<AB>(8);
            let n_tv = r.n(c.tv);
            let n_s = r.n(c.ssum);
            let mut t = b.when_transition();
            t.assert_zero(nisf);
            t.assert_zero(nact.clone() * (one.clone() - act.clone()));
            t.assert_zero(nact.clone() * (nid - v(c.nid) - one.clone()));
            t.assert_eq(lastn.clone(), act.clone() * (one.clone() - nact.clone()));
            t.assert_zero(nact * (n_s - v(c.ssum) - n_len - n_tv * k::<AB>(72)));
        }
        let slack = v(c.wsd[0]) + v(c.wsd[1]) * k::<AB>(256) + v(c.wsd[2]) * k::<AB>(65536);
        b.assert_zero(lastn.clone() * (k::<AB>(MAX_WITNESS_BYTES as u64) - v(c.ssum) - slack));
        for &x in &c.wsd {
            query(b, BUS_RANGE8, vec![v(x)], lastn.clone());
        }

        // ---- digests ----------------------------------------------------------------------
        let npre = |id: AB::Expr| k::<AB>(msg_id(K_NPRE, 0) as u64) + id;
        let npost = |id: AB::Expr| k::<AB>(msg_id(K_NPOST, 0) as u64) + id;
        let mut q = vec![npre(v(c.nid))];
        q.extend(limbs_from_bytes::<AB>(&pvs[PV_PRE..PV_PRE + 32]));
        query(b, BUS_DIGEST, q, isf.clone());
        let mut q = vec![npost(v(c.nid))];
        q.extend(limbs_from_bytes::<AB>(&pvs[PV_POST..PV_POST + 32]));
        query(b, BUS_DIGEST, q, isf.clone());
        for j in 0..16 {
            let rv = v(c.rv[j]);
            let mut q = vec![npre(v(c.cid[j]))];
            q.extend(limbs_from_bytes::<AB>(&vs(&c.w[j])));
            query(b, BUS_DIGEST, q, rv.clone());
            let mut q = vec![npost(v(c.cid[j]))];
            q.extend(limbs_from_bytes::<AB>(&vs(&c.pw[j])));
            query(b, BUS_DIGEST, q, rv);
        }
        let mut q = vec![k::<AB>(msg_id(K_VPRE, 0) as u64) + v(c.vk)];
        q.extend(limbs_from_bytes::<AB>(&vs(&c.vh)));
        query(b, BUS_DIGEST, q, tv.clone());
        let mut q = vec![k::<AB>(msg_id(K_VPOST, 0) as u64) + v(c.vk)];
        q.extend(limbs_from_bytes::<AB>(&vs(&c.pvh)));
        query(b, BUS_DIGEST, q, tv.clone());

        // ---- walk edges / slots -------------------------------------------------------
        let nid = v(c.nid);
        for j in 0..16 {
            provide(
                b,
                BUS_EDGE,
                vec![nid.clone(), AB::Expr::ZERO, k::<AB>(j as u64), v(c.cid[j]), AB::Expr::ZERO],
                v(c.me[j]),
            );
        }
        let m_nib = v(c.m_nib);
        provide(
            b,
            BUS_EDGE,
            vec![nid.clone(), AB::Expr::ZERO, v(c.x0), nid.clone(), one.clone()],
            m_nib.clone() * odd.clone(),
        );
        for m in 0..MAX_KEY_BYTES {
            let ih = k::<AB>(2 * m as u64) + odd.clone();
            provide(
                b,
                BUS_EDGE,
                vec![nid.clone(), ih.clone(), khi[m].clone(), nid.clone(), ih.clone() + one.clone()],
                m_nib.clone() * kb[m].clone(),
            );
            provide(
                b,
                BUS_EDGE,
                vec![
                    nid.clone(),
                    ih.clone() + one.clone(),
                    klo[m].clone(),
                    nid.clone(),
                    ih + AB::Expr::TWO,
                ],
                m_nib.clone() * kb[m].clone(),
            );
        }
        provide(
            b,
            BUS_EPS,
            vec![nid.clone(), s.clone(), v(c.cid[0]), AB::Expr::ZERO],
            v(c.m_eps),
        );
        send(b, BUS_VSLOT, vec![nid.clone(), tl.clone() * s, v(c.vk)], tv.clone());

        // ---- emissions ------------------------------------------------------------------------
        let pre_msg = npre(nid.clone());
        let post_msg = npost(nid);
        let tag = tb1.clone() + tb2.clone() * AB::Expr::TWO + te.clone() * k::<AB>(3);
        let hp0 = tl.clone() * k::<AB>(32) + odd.clone() * k::<AB>(16) + v(c.x0);
        let bm_lo = (0..8).rev().fold(AB::Expr::ZERO, |a, j| a * AB::Expr::TWO + bm[j].clone());
        let bm_hi = (8..16).rev().fold(AB::Expr::ZERO, |a, j| a * AB::Expr::TWO + bm[j].clone());
        let p_bm = tb1.clone() + tb2.clone() * k::<AB>(37);
        for (msg, post) in [(&pre_msg, false), (&post_msg, true)] {
            let em = |b: &mut AB, pos: AB::Expr, byte: AB::Expr, gate: AB::Expr| {
                send(b, BUS_BYTES, vec![msg.clone(), pos, byte], gate);
            };
            em(b, AB::Expr::ZERO, tag.clone(), act.clone());
            em(b, one.clone(), hplen.clone(), le.clone());
            for i in 2..5 {
                em(b, k::<AB>(i), AB::Expr::ZERO, le.clone());
            }
            em(b, k::<AB>(5), hp0.clone(), le.clone());
            for m in 0..MAX_KEY_BYTES {
                em(
                    b,
                    k::<AB>(6 + m as u64),
                    khi[m].clone() * k::<AB>(16) + klo[m].clone(),
                    kb[m].clone(),
                );
            }
            for i in 0..4 {
                em(b, v(c.pv_) + k::<AB>(i as u64), v(c.vlen[i]), gv.clone());
            }
            for i in 0..32 {
                let x = if post { v(c.pvh[i]) } else { v(c.vh[i]) };
                em(b, v(c.pv_) + k::<AB>(4 + i as u64), x, gv.clone());
            }
            em(b, p_bm.clone(), bm_lo.clone(), br.clone());
            em(b, p_bm.clone() + one.clone(), bm_hi.clone(), br.clone());
            for j in 0..16 {
                let base = v(c.pc) + pcs[j].clone() * k::<AB>(32);
                for i in 0..32 {
                    let x = if post { v(c.pw[j][i]) } else { v(c.w[j][i]) };
                    em(b, base.clone() + k::<AB>(i as u64), x, slot_act[j].clone());
                }
            }
            for i in 0..8 {
                em(b, v(c.pm) + k::<AB>(i as u64), v(c.mem[i]), act.clone());
            }
        }
    }
}

