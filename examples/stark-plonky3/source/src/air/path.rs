//! PATH table: the trie walk of every account key, one row per key nibble.
//!
//! A walk state is `(node, i)`: "at node `node`, having consumed `i` nibbles
//! of its own key segment" (branches: always `i = 0`). Each row consumes the
//! account's nibble `t` (`BUS_KEYNIB`, sent by ACCT) along an edge
//! `(N, i) --nib--> (N2, i2)` provided by the node's own bytes (`BUS_EDGE`),
//! optionally followed by an extension's epsilon move `(N2, i2) -> (N3, i3)`
//! (`BUS_EPS`, extension end -> its child). Walks start at the root state
//! `(0, 0)` and the last row of a walk sends its end state on `BUS_FINAL`.

use super::*;
use crate::consts::*;

pub struct PathCols {
    pub act: usize,
    pub isf: usize,
    pub start: usize,
    pub end: usize,
    pub k: usize,
    pub t: usize,
    pub nib: usize,
    pub n: usize,
    pub i: usize,
    pub n2: usize,
    pub i2: usize,
    pub jump: usize,
    pub n3: usize,
    pub i3: usize,
    pub width: usize,
}

impl PathCols {
    pub fn new() -> Self {
        let mut a = Alloc::default();
        let mut c = PathCols {
            act: a.one(),
            isf: a.one(),
            start: a.one(),
            end: a.one(),
            k: a.one(),
            t: a.one(),
            nib: a.one(),
            n: a.one(),
            i: a.one(),
            n2: a.one(),
            i2: a.one(),
            jump: a.one(),
            n3: a.one(),
            i3: a.one(),
            width: 0,
        };
        c.width = a.0;
        c
    }
}

#[derive(Clone)]
pub struct PathAir {
    pub c: std::sync::Arc<PathCols>,
}

impl PathAir {
    pub fn new() -> Self {
        PathAir { c: std::sync::Arc::new(PathCols::new()) }
    }
    pub fn width(&self) -> usize {
        self.c.width
    }
    pub fn eval<AB: AirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        let c = &*self.c;
        let r = Rows::<AB>::new(b, true);
        let v = |i: usize| r.c(i);
        let one = AB::Expr::ONE;
        let (act, isf, start, end, jump) = (v(c.act), v(c.isf), v(c.start), v(c.end), v(c.jump));
        for x in [&act, &isf, &start, &end, &jump] {
            b.assert_bool(x.clone());
        }
        b.when_first_row().assert_one(isf.clone());
        b.when_first_row().assert_one(act.clone());
        b.when_first_row().assert_one(start.clone());
        b.assert_zero((one.clone() - act.clone()) * start.clone());
        b.assert_zero((one.clone() - act.clone()) * end.clone());
        b.assert_zero((one.clone() - act.clone()) * jump.clone());
        b.assert_zero(start.clone() * v(c.t));
        b.assert_zero(start.clone() * v(c.n));
        b.assert_zero(start.clone() * v(c.i));
        b.assert_zero((one.clone() - jump.clone()) * (v(c.n3) - v(c.n2)));
        b.assert_zero((one.clone() - jump.clone()) * (v(c.i3) - v(c.i2)));
        b.when_last_row().assert_zero(act.clone() * (one.clone() - end.clone()));
        {
            let (nact, nstart, nk, nt, nn, ni, nisf) =
                (r.n(c.act), r.n(c.start), r.n(c.k), r.n(c.t), r.n(c.n), r.n(c.i), r.n(c.isf));
            let mut t = b.when_transition();
            t.assert_zero(nisf);
            t.assert_zero(nact.clone() * (one.clone() - act.clone()));
            let cont = nact.clone() * (one.clone() - nstart.clone());
            t.assert_zero(cont.clone() * (nk - v(c.k)));
            t.assert_zero(cont.clone() * (nt - v(c.t) - one.clone()));
            t.assert_zero(cont.clone() * (nn - v(c.n3)));
            t.assert_zero(cont.clone() * (ni - v(c.i3)));
            t.assert_zero(cont * end.clone());
            t.assert_zero(nstart * act.clone() * (one.clone() - end.clone()));
            t.assert_zero(act.clone() * (one.clone() - nact) * (one.clone() - end.clone()));
        }
        zero_inactive(b, &r, c.act, &[]);
        recv(b, BUS_KEYNIB, vec![v(c.k), v(c.t), v(c.nib)], act.clone());
        query(b, BUS_EDGE, vec![v(c.n), v(c.i), v(c.nib), v(c.n2), v(c.i2)], act);
        query(b, BUS_EPS, vec![v(c.n2), v(c.i2), v(c.n3), v(c.i3)], jump);
        send(b, BUS_FINAL, vec![v(c.k), v(c.n3), v(c.i3)], end);
    }
}
