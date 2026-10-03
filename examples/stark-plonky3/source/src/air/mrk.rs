//! MRK table: nearcore `merklize` over the outcome leaves.
//!
//! Rows enumerate the tree level by level: level `j` (1-based) has
//! `s = ceil(sp / 2)` nodes where `sp` is the size of level `j-1` (`sp = n`
//! for level 1, from the public values). Node `(j, i)` is
//! `sha256(node(j-1, 2i) ‖ node(j-1, 2i+1))`, except the last node of an odd
//! level, which is promoted unchanged. Node positions are published on
//! `BUS_MPOS (level, index, msg)` (leaves by RCPT); the level of size 1 is the
//! root and its digest must equal the public `outcome_root`.

use super::*;
use crate::consts::*;

pub struct MrkCols {
    pub act: usize,
    pub isf: usize,
    pub j: usize,
    pub i: usize,
    pub sp: usize,
    pub s: usize,
    pub odd: usize,
    pub lil: usize,
    pub root: usize,
    pub rinv: usize,
    pub idx: usize,
    pub msg_l: usize,
    pub msg_r: usize,
    pub own: usize,
    pub l: Vec<usize>,
    pub rr: Vec<usize>,
    pub m_prov: usize,
    pub width: usize,
}

impl MrkCols {
    pub fn new() -> Self {
        let mut a = Alloc::default();
        let mut c = MrkCols {
            act: a.one(),
            isf: a.one(),
            j: a.one(),
            i: a.one(),
            sp: a.one(),
            s: a.one(),
            odd: a.one(),
            lil: a.one(),
            root: a.one(),
            rinv: a.one(),
            idx: a.one(),
            msg_l: a.one(),
            msg_r: a.one(),
            own: a.one(),
            l: a.vec(32),
            rr: a.vec(32),
            m_prov: a.one(),
            width: 0,
        };
        c.width = a.0;
        c
    }
}

#[derive(Clone)]
pub struct MrkAir {
    pub c: std::sync::Arc<MrkCols>,
}

impl MrkAir {
    pub fn new() -> Self {
        MrkAir { c: std::sync::Arc::new(MrkCols::new()) }
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
        let (act, isf, odd, lil, root) = (v(c.act), v(c.isf), v(c.odd), v(c.lil), v(c.root));
        for x in [&act, &isf, &odd, &lil, &root] {
            b.assert_bool(x.clone());
        }
        let mut n_pub = AB::Expr::ZERO;
        for i in (0..4).rev() {
            n_pub = n_pub * k::<AB>(256) + pvs[PV_N + i].clone();
        }
        {
            let mut f = b.when_first_row();
            f.assert_one(isf.clone());
            f.assert_one(act.clone());
            f.assert_one(v(c.j));
            f.assert_zero(v(c.i));
            f.assert_eq(v(c.sp), n_pub);
            f.assert_zero(v(c.idx));
        }
        b.assert_zero(act.clone() * (v(c.sp) - v(c.s) * AB::Expr::TWO + odd.clone()));
        b.assert_zero(lil.clone() * (v(c.i) - v(c.s) + one.clone()));
        b.assert_zero((v(c.s) - one.clone()) * root.clone());
        b.assert_zero(act.clone() * ((v(c.s) - one.clone()) * v(c.rinv) - (one.clone() - root.clone())));
        b.assert_zero(root.clone() * (one.clone() - lil.clone()));
        b.assert_zero((one.clone() - act.clone()) * root.clone());
        let promote = odd.clone() * lil.clone();
        let hashrow = act.clone() * (one.clone() - promote.clone());
        let own_hash = k::<AB>(msg_id(K_MRK, 0) as u64) + v(c.idx);
        b.assert_zero(
            act.clone()
                * (v(c.own) - promote.clone() * v(c.msg_l) - (one.clone() - promote.clone()) * own_hash.clone()),
        );
        b.when_last_row().assert_zero(act.clone() * (one.clone() - root.clone()));
        {
            let (nact, nj, ni, nsp, ns, nodd, nidx, nisf) =
                (r.n(c.act), r.n(c.j), r.n(c.i), r.n(c.sp), r.n(c.s), r.n(c.odd), r.n(c.idx), r.n(c.isf));
            let mut t = b.when_transition();
            t.assert_zero(nisf);
            t.assert_eq(nidx, v(c.idx) + one.clone());
            t.assert_zero(nact.clone() * (one.clone() - act.clone()));
            t.assert_zero(root.clone() * nact.clone());
            t.assert_zero(act.clone() * (one.clone() - root.clone()) * (one.clone() - nact.clone()));
            let same = nact.clone() * (one.clone() - lil.clone());
            t.assert_zero(same.clone() * (nj.clone() - v(c.j)));
            t.assert_zero(same.clone() * (ni.clone() - v(c.i) - one.clone()));
            t.assert_zero(same.clone() * (nsp.clone() - v(c.sp)));
            t.assert_zero(same.clone() * (ns - v(c.s)));
            t.assert_zero(same * (nodd - odd.clone()));
            let up = nact * lil.clone();
            t.assert_zero(up.clone() * (nj - v(c.j) - one.clone()));
            t.assert_zero(up.clone() * ni);
            t.assert_zero(up * (nsp - v(c.s)));
        }
        for &x in c.l.iter().chain(c.rr.iter()).chain([c.msg_r].iter()) {
            b.assert_zero((one.clone() - hashrow.clone()) * v(x));
        }
        b.assert_zero(root.clone() * v(c.rinv));
        zero_inactive(b, &r, c.act, &[c.idx]);
        let jm1 = v(c.j) - one.clone();
        let two_i = v(c.i) * AB::Expr::TWO;
        query(b, BUS_MPOS, vec![jm1.clone(), two_i.clone(), v(c.msg_l)], act.clone());
        query(b, BUS_MPOS, vec![jm1, two_i + one.clone(), v(c.msg_r)], hashrow.clone());
        provide(b, BUS_MPOS, vec![v(c.j), v(c.i), v(c.own)], v(c.m_prov));
        b.assert_zero((one.clone() - act.clone()) * v(c.m_prov));
        let l = vs(&c.l);
        let rr = vs(&c.rr);
        let mut ql = vec![v(c.msg_l)];
        ql.extend(limbs_from_bytes::<AB>(&l));
        query(b, BUS_DIGEST, ql, hashrow.clone());
        let mut qr = vec![v(c.msg_r)];
        qr.extend(limbs_from_bytes::<AB>(&rr));
        query(b, BUS_DIGEST, qr, hashrow.clone());
        let mut qroot = vec![v(c.own)];
        qroot.extend(limbs_from_bytes::<AB>(&pvs[PV_OUT..PV_OUT + 32]));
        query(b, BUS_DIGEST, qroot, root);
        for i in 0..32 {
            send(b, BUS_BYTES, vec![own_hash.clone(), k::<AB>(i as u64), l[i].clone()], hashrow.clone());
            send(b, BUS_BYTES, vec![own_hash.clone(), k::<AB>(32 + i as u64), rr[i].clone()], hashrow.clone());
        }
    }
}
