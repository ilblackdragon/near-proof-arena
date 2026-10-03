//! ACCT table: one row per distinct receiver account `k`.
//!
//! * provides `BUS_ACCT (k, len, packed id, locked, storage_usage)` to RCPT;
//! * emits the 72-byte AccountV1 value before (`K_VPRE|k`) and after
//!   (`K_VPOST|k`, only `amount` differs) the batch;
//! * opens and closes the account's amount chain on `BUS_MEM`
//!   (`(k, 0, amount_pre)` written, `(k, t_last, amount_post)` read);
//! * sends the trie key nibbles of `0x00 ‖ account_id` on `BUS_KEYNIB` and
//!   receives the walk's end state on `BUS_FINAL` and the value slot of that
//!   state on `BUS_VSLOT` (one slot per account, so two accounts can never
//!   share a slot).

use super::*;
use crate::consts::*;

pub struct AcctCols {
    pub act: usize,
    pub isf: usize,
    pub k: usize,
    pub a: Vec<usize>,
    pub c: Vec<usize>,
    pub hi: Vec<usize>,
    pub lo: Vec<usize>,
    pub val: Vec<usize>,
    pub post: Vec<usize>,
    pub o: usize,
    pub io: usize,
    pub t_last: usize,
    pub m_acct: usize,
    pub inv_max: usize,
    pub width: usize,
}

impl AcctCols {
    pub fn new() -> Self {
        let mut a = Alloc::default();
        let mut c = AcctCols {
            act: a.one(),
            isf: a.one(),
            k: a.one(),
            a: a.vec(64),
            c: a.vec(64),
            hi: a.vec(64),
            lo: a.vec(64),
            val: a.vec(72),
            post: a.vec(16),
            o: a.one(),
            io: a.one(),
            t_last: a.one(),
            m_acct: a.one(),
            inv_max: a.one(),
            width: 0,
        };
        c.width = a.0;
        c
    }
}

#[derive(Clone)]
pub struct AcctAir {
    pub c: std::sync::Arc<AcctCols>,
}

impl AcctAir {
    pub fn new() -> Self {
        AcctAir { c: std::sync::Arc::new(AcctCols::new()) }
    }
    pub fn width(&self) -> usize {
        self.c.width
    }
    pub fn eval<AB: AirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        let c = &*self.c;
        let r = Rows::<AB>::new(b, true);
        let v = |i: usize| r.c(i);
        let vs = |ix: &[usize]| -> Vec<AB::Expr> { ix.iter().map(|&i| r.c(i)).collect() };
        let one = AB::Expr::ONE;
        let (act, isf) = (v(c.act), v(c.isf));
        b.assert_bool(act.clone());
        b.assert_bool(isf.clone());
        b.when_first_row().assert_one(isf.clone());
        b.when_first_row().assert_one(act.clone());
        b.when_first_row().assert_zero(v(c.k));
        {
            let (nact, nk, nisf) = (r.n(c.act), r.n(c.k), r.n(c.isf));
            let mut t = b.when_transition();
            t.assert_zero(nisf);
            t.assert_zero(nact.clone() * (one.clone() - act.clone()));
            t.assert_zero(nact * (nk - v(c.k) - one.clone()));
        }
        let a = vs(&c.a);
        let ch = vs(&c.c);
        for i in 0..64 {
            b.assert_bool(a[i].clone());
            if i + 1 < 64 {
                b.assert_zero(a[i + 1].clone() * (one.clone() - a[i].clone()));
            }
            b.assert_zero((one.clone() - a[i].clone()) * ch[i].clone());
            query(b, BUS_NIB, vec![ch[i].clone(), v(c.hi[i]), v(c.lo[i])], a[i].clone());
        }
        b.assert_zero(act.clone() * (one.clone() - a[0].clone()));
        b.assert_zero(act.clone() * (one.clone() - a[1].clone()));
        let len = a.iter().fold(AB::Expr::ZERO, |acc, x| acc + x.clone());
        let val = vs(&c.val);
        let post = vs(&c.post);
        // ACCT entry
        let mut entry = vec![v(c.k), len];
        for j in 0..PACK_LIMBS {
            let mut acc = AB::Expr::ZERO;
            for t in (0..3).rev() {
                let idx = 3 * j + t;
                let x = if idx < 64 { ch[idx].clone() } else { AB::Expr::ZERO };
                acc = acc * k::<AB>(256) + x;
            }
            entry.push(acc);
        }
        entry.extend_from_slice(&val[16..32]);
        entry.extend_from_slice(&val[64..72]);
        provide(b, BUS_ACCT, entry, v(c.m_acct));
        b.assert_zero((one.clone() - act.clone()) * v(c.m_acct));
        // AccountV1: pre amount != u128::MAX
        let notmax = val[..16].iter().fold(AB::Expr::ZERO, |acc, x| acc + k::<AB>(255) - x.clone());
        b.assert_zero(act.clone() * (notmax * v(c.inv_max) - one.clone()));
        // values
        let vpre = k::<AB>(msg_id(K_VPRE, 0) as u64) + v(c.k);
        let vpost = k::<AB>(msg_id(K_VPOST, 0) as u64) + v(c.k);
        for i in 0..72 {
            send(b, BUS_BYTES, vec![vpre.clone(), k::<AB>(i as u64), val[i].clone()], act.clone());
            let pb = if i < 16 { post[i].clone() } else { val[i].clone() };
            send(b, BUS_BYTES, vec![vpost.clone(), k::<AB>(i as u64), pb], act.clone());
        }
        // amount chain
        let mut w0 = vec![v(c.k), AB::Expr::ZERO];
        w0.extend_from_slice(&val[..16]);
        send(b, BUS_MEM, w0, act.clone());
        let mut rl = vec![v(c.k), v(c.t_last)];
        rl.extend(post.clone());
        recv(b, BUS_MEM, rl, act.clone());
        // key nibbles of 0x00 ‖ id
        send(b, BUS_KEYNIB, vec![v(c.k), AB::Expr::ZERO, AB::Expr::ZERO], act.clone());
        send(b, BUS_KEYNIB, vec![v(c.k), one.clone(), AB::Expr::ZERO], act.clone());
        for i in 0..64 {
            send(b, BUS_KEYNIB, vec![v(c.k), k::<AB>(2 + 2 * i as u64), v(c.hi[i])], a[i].clone());
            send(b, BUS_KEYNIB, vec![v(c.k), k::<AB>(3 + 2 * i as u64), v(c.lo[i])], a[i].clone());
        }
        recv(b, BUS_FINAL, vec![v(c.k), v(c.o), v(c.io)], act.clone());
        recv(b, BUS_VSLOT, vec![v(c.o), v(c.io), v(c.k)], act);
    }
}
