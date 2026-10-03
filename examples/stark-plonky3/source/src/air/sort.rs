//! SORT table: the receipt ids, strictly increasing (as 256-bit
//! little-endian integers), received from RCPT on `BUS_RIDS`. A permutation
//! of the batch's ids that is strictly increasing proves they are pairwise
//! distinct (`distinct_receipt_ids`).
//!
//! Row `t > 0` holds `diff` and carries with `rid_t = rid_{t-1} + diff + 1`.

use super::*;
use crate::consts::*;

pub struct SortCols {
    pub act: usize,
    pub isf: usize,
    pub rid: Vec<usize>,
    pub diff: Vec<usize>,
    pub cs: Vec<usize>,
    pub width: usize,
}

impl SortCols {
    pub fn new() -> Self {
        let mut a = Alloc::default();
        let mut c = SortCols {
            act: a.one(),
            isf: a.one(),
            rid: a.vec(32),
            diff: a.vec(32),
            cs: a.vec(31),
            width: 0,
        };
        c.width = a.0;
        c
    }
}

#[derive(Clone)]
pub struct SortAir {
    pub c: std::sync::Arc<SortCols>,
}

impl SortAir {
    pub fn new() -> Self {
        SortAir { c: std::sync::Arc::new(SortCols::new()) }
    }
    pub fn width(&self) -> usize {
        self.c.width
    }
    pub fn eval<AB: AirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        let c = &*self.c;
        let r = Rows::<AB>::new(b, true);
        let v = |i: usize| r.c(i);
        let vs = |ix: &[usize]| -> Vec<AB::Expr> { ix.iter().map(|&i| r.c(i)).collect() };
        let ns = |ix: &[usize]| -> Vec<AB::Expr> { ix.iter().map(|&i| r.n(i)).collect() };
        let one = AB::Expr::ONE;
        let (act, isf) = (v(c.act), v(c.isf));
        b.assert_bool(act.clone());
        b.assert_bool(isf.clone());
        b.when_first_row().assert_one(isf.clone());
        b.when_first_row().assert_one(act.clone());
        {
            let nact = r.n(c.act);
            let (nrid, ndiff, ncs) = (ns(&c.rid), ns(&c.diff), ns(&c.cs));
            let rid = vs(&c.rid);
            let nisf = r.n(c.isf);
            let mut t = b.when_transition();
            t.assert_zero(nisf);
            t.assert_zero(nact.clone() * (one.clone() - act.clone()));
            assert_add_bytes(&mut t, nact, &rid, &ndiff, one.clone(), &nrid, &ncs);
        }
        recv(b, BUS_RIDS, vs(&c.rid), act.clone());
        let has_prev = act * (one - isf);
        for &d in &c.diff {
            query(b, BUS_RANGE8, vec![v(d)], has_prev.clone());
        }
    }
}
