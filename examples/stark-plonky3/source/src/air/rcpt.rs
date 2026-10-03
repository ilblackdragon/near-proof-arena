//! RCPT table: one row per receipt, in batch order.
//!
//! Each row holds the receipt's fields and
//!
//! * emits its exact nearcore borsh bytes into the receipts-commitment
//!   message (`K_RC`, at running offset `o`; row 0 also emits the
//!   `u64 shard_id ‖ u32 n` header from the public values);
//! * emits the receipt's `PartialExecutionOutcome` (`K_PEO|r`), outcome
//!   leaf (`K_LEAF|r`), refund-id preimage (`K_RID|r`, if a refund) and gas
//!   refund receipt (into `K_RF` at running offset `o2`, if a refund);
//! * checks the domain conditions on its own fields (account-id grammar,
//!   predecessor != "system", named receiver, key type);
//! * does the gas arithmetic: `p = min(gas_price, block_gas_price)`, the
//!   refund flag `hr = [gas_price > block_gas_price]`, `burnt = G*p`,
//!   refund amount `G*(gas_price-p)` (no u128 overflow), running
//!   `tokens_burnt_total` and `refund_count`;
//! * reads its receiver account (`BUS_ACCT`) and applies the deposit through
//!   the offline memory argument on `BUS_MEM` (read `(k, t_prev, before)`,
//!   write `(k, r+1, after)`, `t_prev <= r`), with the per-step overflow,
//!   `u128::MAX`-sentinel and storage-stake checks.

use super::*;
use crate::consts::*;

pub struct StrCols {
    pub a: Vec<usize>,
    pub c: Vec<usize>,
    pub cls: Vec<usize>,
}

impl StrCols {
    fn new(al: &mut Alloc) -> Self {
        StrCols { a: al.vec(64), c: al.vec(64), cls: al.vec(64) }
    }
}

pub struct RcptCols {
    pub act: usize,
    pub isf: usize,
    pub lastr: usize,
    pub r: usize,
    pub o: usize,
    pub o2: usize,
    pub sp: StrCols,
    pub sv: StrCols,
    pub ss: StrCols,
    pub hexcnt: usize,
    pub hexcnt2: usize,
    pub inv_sys: usize,
    pub inv_n: [usize; 3],
    pub rid: Vec<usize>,
    pub kt: usize,
    pub pk: Vec<usize>,
    pub gp: Vec<usize>,
    pub dep: Vec<usize>,
    pub hr: usize,
    pub d: Vec<usize>,
    pub cd: Vec<usize>,
    pub dinv: usize,
    pub burnt: Vec<usize>,
    pub cb: Vec<usize>,
    pub ramt: Vec<usize>,
    pub cr: Vec<usize>,
    pub t: Vec<usize>,
    pub ct: Vec<usize>,
    pub rf: usize,
    pub refund_id: Vec<usize>,
    pub peo_dig: Vec<usize>,
    pub kacc: usize,
    pub locked: Vec<usize>,
    pub storage: Vec<usize>,
    pub t_prev: usize,
    pub abef: Vec<usize>,
    pub aaft: Vec<usize>,
    pub ca: Vec<usize>,
    pub tot: Vec<usize>,
    pub ctot: Vec<usize>,
    pub inv_max: usize,
    pub sz: usize,
    pub q: Vec<usize>,
    pub cq: Vec<usize>,
    pub e: Vec<usize>,
    pub ce: Vec<usize>,
    pub m_leaf: usize,
    pub width: usize,
}

impl RcptCols {
    pub fn new() -> Self {
        let mut a = Alloc::default();
        let mut c = RcptCols {
            act: a.one(),
            isf: a.one(),
            lastr: a.one(),
            r: a.one(),
            o: a.one(),
            o2: a.one(),
            sp: StrCols::new(&mut a),
            sv: StrCols::new(&mut a),
            ss: StrCols::new(&mut a),
            hexcnt: a.one(),
            hexcnt2: a.one(),
            inv_sys: a.one(),
            inv_n: a.arr(),
            rid: a.vec(32),
            kt: a.one(),
            pk: a.vec(64),
            gp: a.vec(16),
            dep: a.vec(16),
            hr: a.one(),
            d: a.vec(16),
            cd: a.vec(15),
            dinv: a.one(),
            burnt: a.vec(16),
            cb: a.vec(mul_carries(16, 5)),
            ramt: a.vec(16),
            cr: a.vec(mul_carries(16, 5)),
            t: a.vec(16),
            ct: a.vec(15),
            rf: a.one(),
            refund_id: a.vec(32),
            peo_dig: a.vec(32),
            kacc: a.one(),
            locked: a.vec(16),
            storage: a.vec(8),
            t_prev: a.one(),
            abef: a.vec(16),
            aaft: a.vec(16),
            ca: a.vec(15),
            tot: a.vec(16),
            ctot: a.vec(15),
            inv_max: a.one(),
            sz: a.one(),
            q: a.vec(16),
            cq: a.vec(mul_carries(8, 8)),
            e: a.vec(16),
            ce: a.vec(15),
            m_leaf: a.one(),
            width: 0,
        };
        c.width = a.0;
        c
    }
}

pub const SYSTEM: &[u8; 6] = b"system";
/// Fixed part of a receipt's serialized size (see module docs).
pub const RC_FIXED: u64 = 123;
pub const RF_FIXED: u64 = 129;

#[derive(Clone)]
pub struct RcptAir {
    pub c: std::sync::Arc<RcptCols>,
}

impl RcptAir {
    pub fn new() -> Self {
        RcptAir { c: std::sync::Arc::new(RcptCols::new()) }
    }
    pub fn width(&self) -> usize {
        self.c.width
    }

    pub fn eval<AB: AirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        let c = &*self.c;
        let r = Rows::<AB>::new(b, true);
        let pvs: Vec<AB::Expr> = (0..NUM_PV).map(|i| pv::<AB>(b, i)).collect();
        let pvle = |off: usize, len: usize| -> AB::Expr {
            let mut acc = AB::Expr::ZERO;
            for i in (0..len).rev() {
                acc = acc * AB::Expr::from_u32(256) + pvs[off + i].clone();
            }
            acc
        };
        let pvdig = |off: usize| -> Vec<AB::Expr> { limbs_from_bytes::<AB>(&pvs[off..off + 32]) };
        let v = |i: usize| r.c(i);
        let vs = |ix: &[usize]| -> Vec<AB::Expr> { ix.iter().map(|&i| r.c(i)).collect() };
        let one = AB::Expr::ONE;
        let act = v(c.act);
        let hr = v(c.hr);
        let kt = v(c.kt);
        let isf = v(c.isf);

        // ---- row structure -------------------------------------------------
        b.assert_bool(act.clone());
        b.assert_bool(isf.clone());
        b.assert_bool(v(c.lastr));
        b.assert_bool(hr.clone());
        b.assert_bool(kt.clone());
        b.assert_bool(v(c.sz));
        b.when_first_row().assert_one(isf.clone());
        b.when_first_row().assert_one(act.clone());
        b.when_first_row().assert_zero(v(c.r));
        b.when_first_row().assert_eq(v(c.o), k::<AB>(12));
        b.when_first_row().assert_eq(v(c.o2), k::<AB>(4));
        b.when_first_row().assert_eq(v(c.rf), hr.clone());
        for i in 0..16 {
            b.when_first_row().assert_eq(v(c.t[i]), v(c.burnt[i]));
        }
        b.when_last_row().assert_eq(v(c.lastr), act.clone());
        {
            let nact = r.n(c.act);
            let mut t = b.when_transition();
            t.assert_zero(r.n(c.isf));
            t.assert_zero(nact.clone() * (one.clone() - act.clone()));
            t.assert_eq(v(c.lastr), act.clone() * (one.clone() - nact.clone()));
            t.assert_zero(nact.clone() * (r.n(c.r) - v(c.r) - one.clone()));
        }
        let n_pub = pvle(PV_N, 4);
        b.assert_zero(v(c.lastr) * (v(c.r) + one.clone() - n_pub));

        // ---- account-id strings ---------------------------------------------
        // 2 * [x == 2] for x in {0,1,2}
        let sep_of = |x: AB::Expr| -> AB::Expr { x.clone() * x.clone() - x };
        let hex_of = |x: AB::Expr| -> AB::Expr { x.clone() * (AB::Expr::TWO - x) };
        for s in [&c.sp, &c.sv, &c.ss] {
            let a = vs(&s.a);
            let ch = vs(&s.c);
            let cl = vs(&s.cls);
            for i in 0..64 {
                b.assert_bool(a[i].clone());
                if i + 1 < 64 {
                    b.assert_zero(a[i + 1].clone() * (one.clone() - a[i].clone()));
                }
                b.assert_zero((one.clone() - a[i].clone()) * ch[i].clone());
                b.assert_zero(
                    cl[i].clone() * (cl[i].clone() - one.clone()) * (cl[i].clone() - AB::Expr::TWO),
                );
                query(b, BUS_CLASS, vec![ch[i].clone(), cl[i].clone()], a[i].clone());
                if i + 1 < 64 {
                    b.assert_zero(sep_of(cl[i].clone()) * sep_of(cl[i + 1].clone()));
                }
                let next_a = if i + 1 < 64 { a[i + 1].clone() } else { AB::Expr::ZERO };
                b.assert_zero((a[i].clone() - next_a) * sep_of(cl[i].clone()));
            }
            b.assert_zero(act.clone() * (one.clone() - a[0].clone()));
            b.assert_zero(act.clone() * (one.clone() - a[1].clone()));
            b.assert_zero(sep_of(cl[0].clone()));
            for i in 0..64 {
                b.assert_zero((one.clone() - a[i].clone()) * cl[i].clone());
            }
        }
        let len = |s: &StrCols| s.a.iter().fold(AB::Expr::ZERO, |acc, &i| acc + v(i));
        let (lp, lv, ls) = (len(&c.sp), len(&c.sv), len(&c.ss));
        // predecessor != "system"
        {
            let mut val = (lp.clone() - k::<AB>(6)) * (lp.clone() - k::<AB>(6));
            for (i, &ch) in SYSTEM.iter().enumerate() {
                let d = v(c.sp.c[i]) - k::<AB>(ch as u64);
                val = val + d.clone() * d;
            }
            b.assert_zero(act.clone() * (val * v(c.inv_sys) - one.clone()));
        }
        // named receiver: not 64-hex, not "0x"+40hex, not "0s"+40hex
        {
            let mut h = AB::Expr::ZERO;
            let mut h2 = AB::Expr::ZERO;
            for i in 0..64 {
                let t = v(c.sv.a[i]) * hex_of(v(c.sv.cls[i]));
                if i >= 2 {
                    h2 = h2 + t.clone();
                }
                h = h + t;
            }
            b.assert_eq(v(c.hexcnt), h);
            b.assert_eq(v(c.hexcnt2), h2);
            let sq = |x: AB::Expr| x.clone() * x;
            let p1 = sq(lv.clone() - k::<AB>(64)) + sq(v(c.hexcnt) - lv.clone());
            b.assert_zero(act.clone() * (p1 * v(c.inv_n[0]) - one.clone()));
            for (j, second) in [(1usize, b'x'), (2, b's')] {
                let p = sq(lv.clone() - k::<AB>(42))
                    + sq(v(c.sv.c[0]) - k::<AB>(b'0' as u64))
                    + sq(v(c.sv.c[1]) - k::<AB>(second as u64))
                    + sq(v(c.hexcnt2) - k::<AB>(40));
                b.assert_zero(act.clone() * (p * v(c.inv_n[j]) - one.clone()));
            }
        }
        // key type: unused upper half of an ED25519 key is zero
        for i in 32..64 {
            b.assert_zero((one.clone() - kt.clone()) * v(c.pk[i]));
        }

        // ---- gas arithmetic ---------------------------------------------------
        let gp = vs(&c.gp);
        let bgp: Vec<AB::Expr> = pvs[PV_BGP..PV_BGP + 16].to_vec();
        let xs: Vec<AB::Expr> = (0..16)
            .map(|i| hr.clone() * gp[i].clone() + (one.clone() - hr.clone()) * bgp[i].clone())
            .collect();
        let ys: Vec<AB::Expr> = (0..16)
            .map(|i| hr.clone() * bgp[i].clone() + (one.clone() - hr.clone()) * gp[i].clone())
            .collect();
        let d = vs(&c.d);
        assert_add_bytes(b, act.clone(), &ys, &d, AB::Expr::ZERO, &xs, &vs(&c.cd));
        let dsum = d.iter().fold(AB::Expr::ZERO, |a, x| a + x.clone());
        b.assert_zero(act.clone() * hr.clone() * (dsum * v(c.dinv) - one.clone()));
        let burnt = vs(&c.burnt);
        assert_mul_const(b, &ys, &G_BYTES, &burnt, &vs(&c.cb));
        let surplus: Vec<AB::Expr> = d.iter().map(|x| hr.clone() * x.clone()).collect();
        let ramt = vs(&c.ramt);
        assert_mul_const(b, &surplus, &G_BYTES, &ramt, &vs(&c.cr));
        for i in 0..16 {
            query(b, BUS_RANGE8, vec![d[i].clone()], act.clone());
            query(b, BUS_RANGE8, vec![v(c.t[i])], act.clone());
        }
        for &cc in c.cb.iter().chain(c.cr.iter()) {
            query(b, BUS_RANGE12, vec![v(cc)], act.clone());
        }
        // running tokens_burnt_total and refund_count
        {
            let nact = r.n(c.act);
            let tcur = vs(&c.t);
            let nb: Vec<AB::Expr> = c.burnt.iter().map(|&i| r.n(i)).collect();
            let nt: Vec<AB::Expr> = c.t.iter().map(|&i| r.n(i)).collect();
            let nct: Vec<AB::Expr> = c.ct.iter().map(|&i| r.n(i)).collect();
            let size = k::<AB>(RC_FIXED) + lp.clone() + lv.clone() + ls.clone() + kt.clone() * k::<AB>(32);
            let size2 = k::<AB>(RF_FIXED) + ls.clone() * AB::Expr::TWO + kt.clone() * k::<AB>(32);
            let (n_o, n_o2, n_rf, n_hr) = (r.n(c.o), r.n(c.o2), r.n(c.rf), r.n(c.hr));
            let mut t = b.when_transition();
            assert_add_bytes(&mut t, nact.clone(), &tcur, &nb, AB::Expr::ZERO, &nt, &nct);
            t.assert_zero(nact.clone() * (n_o - v(c.o) - size));
            t.assert_zero(nact.clone() * (n_o2 - v(c.o2) - hr.clone() * size2));
            t.assert_zero(nact.clone() * (n_rf - v(c.rf) - n_hr));
        }
        for i in 0..16 {
            b.assert_zero(v(c.lastr) * (v(c.t[i]) - pvs[PV_TOK + i].clone()));
        }
        let nref = pvle(PV_NREF, 4);
        b.assert_zero(v(c.lastr) * (v(c.rf) - nref));

        // ---- account update -------------------------------------------------
        let packed = |s: &StrCols| -> Vec<AB::Expr> {
            (0..PACK_LIMBS)
                .map(|j| {
                    let mut acc = AB::Expr::ZERO;
                    for t in (0..3).rev() {
                        let idx = 3 * j + t;
                        let x = if idx < 64 { v(s.c[idx]) } else { AB::Expr::ZERO };
                        acc = acc * k::<AB>(256) + x;
                    }
                    acc
                })
                .collect()
        };
        let mut acct = vec![v(c.kacc), lv.clone()];
        acct.extend(packed(&c.sv));
        acct.extend(vs(&c.locked));
        acct.extend(vs(&c.storage));
        query(b, BUS_ACCT, acct, act.clone());
        let mut rd = vec![v(c.kacc), v(c.t_prev)];
        rd.extend(vs(&c.abef));
        recv(b, BUS_MEM, rd, act.clone());
        let mut wr = vec![v(c.kacc), v(c.r) + one.clone()];
        wr.extend(vs(&c.aaft));
        send(b, BUS_MEM, wr, act.clone());
        query(b, BUS_RANGE12, vec![v(c.r) - v(c.t_prev)], act.clone());
        let aaft = vs(&c.aaft);
        assert_add_bytes(b, act.clone(), &vs(&c.abef), &vs(&c.dep), AB::Expr::ZERO, &aaft, &vs(&c.ca));
        let tot = vs(&c.tot);
        assert_add_bytes(b, act.clone(), &aaft, &vs(&c.locked), AB::Expr::ZERO, &tot, &vs(&c.ctot));
        let notmax = aaft.iter().fold(AB::Expr::ZERO, |a, x| a + k::<AB>(255) - x.clone());
        b.assert_zero(act.clone() * (notmax * v(c.inv_max) - one.clone()));
        let st = vs(&c.storage);
        let q = vs(&c.q);
        assert_mul_const(b, &st, &STORAGE_PRICE_BYTES, &q, &vs(&c.cq));
        let sz = v(c.sz);
        let nsz = act.clone() * (one.clone() - sz.clone());
        assert_add_bytes(b, nsz.clone(), &q, &vs(&c.e), AB::Expr::ZERO, &tot, &vs(&c.ce));
        for i in 2..8 {
            b.assert_zero(sz.clone() * st[i].clone());
        }
        query(
            b,
            BUS_RANGE12,
            vec![k::<AB>(770) - st[0].clone() - st[1].clone() * k::<AB>(256)],
            act.clone() * sz.clone(),
        );
        for i in 0..16 {
            query(b, BUS_RANGE8, vec![aaft[i].clone()], act.clone());
            query(b, BUS_RANGE8, vec![tot[i].clone()], act.clone());
            query(b, BUS_RANGE8, vec![q[i].clone()], act.clone());
            query(b, BUS_RANGE8, vec![v(c.e[i])], nsz.clone());
        }
        for &cc in &c.cq {
            query(b, BUS_RANGE12, vec![v(cc)], act.clone());
        }

        // ---- canonical unused witness ------------------------------------------
        let has_prev = act.clone() * (one.clone() - isf.clone());
        for i in 0..15 {
            b.assert_zero((one.clone() - has_prev.clone()) * v(c.ct[i]));
            b.assert_zero((one.clone() - nsz.clone()) * v(c.ce[i]));
        }
        for i in 0..16 {
            b.assert_zero((one.clone() - nsz.clone()) * v(c.e[i]));
            b.assert_zero((one.clone() - hr.clone()) * v(c.ramt[i]));
        }
        for &cc in &c.cr {
            b.assert_zero((one.clone() - hr.clone()) * v(cc));
        }
        for i in 0..32 {
            b.assert_zero((one.clone() - hr.clone()) * v(c.refund_id[i]));
        }
        b.assert_zero((one.clone() - hr.clone()) * v(c.dinv));
        zero_inactive(b, &r, c.act, &[]);

        // ---- links -------------------------------------------------------------
        send(b, BUS_RIDS, vs(&c.rid), act.clone());
        let leaf_msg = k::<AB>(msg_id(K_LEAF, 0) as u64) + v(c.r);
        provide(b, BUS_MPOS, vec![AB::Expr::ZERO, v(c.r), leaf_msg.clone()], v(c.m_leaf));
        b.assert_zero((one.clone() - act.clone()) * v(c.m_leaf));
        let rid_msg = k::<AB>(msg_id(K_RID, 0) as u64) + v(c.r);
        let peo_msg = k::<AB>(msg_id(K_PEO, 0) as u64) + v(c.r);
        let mut q1 = vec![rid_msg.clone()];
        q1.extend(limbs_from_bytes::<AB>(&vs(&c.refund_id)));
        query(b, BUS_DIGEST, q1, hr.clone());
        let mut q2 = vec![peo_msg.clone()];
        q2.extend(limbs_from_bytes::<AB>(&vs(&c.peo_dig)));
        query(b, BUS_DIGEST, q2, act.clone());
        let rc_msg = k::<AB>(msg_id(K_RC, 0) as u64);
        let rf_msg = k::<AB>(msg_id(K_RF, 0) as u64);
        let mut q3 = vec![rc_msg.clone()];
        q3.extend(pvdig(PV_RC));
        query(b, BUS_DIGEST, q3, isf.clone());
        let mut q4 = vec![rf_msg.clone()];
        q4.extend(pvdig(PV_RFC));
        query(b, BUS_DIGEST, q4, isf.clone());

        // ---- emissions -----------------------------------------------------------
        let mut em = |b: &mut AB, msg: &AB::Expr, pos: AB::Expr, byte: AB::Expr, gate: AB::Expr| {
            send(b, BUS_BYTES, vec![msg.clone(), pos, byte], gate);
        };
        let z = || AB::Expr::ZERO;
        // RC header (row 0)
        for i in 0..8 {
            em(b, &rc_msg, k::<AB>(i as u64), pvs[PV_SHARD + i].clone(), isf.clone());
        }
        for i in 0..4 {
            em(b, &rc_msg, k::<AB>(8 + i as u64), pvs[PV_N + i].clone(), isf.clone());
        }
        // RF header (row 0)
        for i in 0..4 {
            em(b, &rf_msg, k::<AB>(i as u64), pvs[PV_NREF + i].clone(), isf.clone());
        }
        // u32 length-prefixed string at `pos`
        let emit_str = |b: &mut AB, em: &mut dyn FnMut(&mut AB, &AB::Expr, AB::Expr, AB::Expr, AB::Expr),
                        msg: &AB::Expr,
                        pos: AB::Expr,
                        s: &StrCols,
                        l: AB::Expr,
                        gate: AB::Expr| {
            em(b, msg, pos.clone(), l, gate.clone());
            for j in 1..4 {
                em(b, msg, pos.clone() + k::<AB>(j), AB::Expr::ZERO, gate.clone());
            }
            for i in 0..64 {
                em(b, msg, pos.clone() + k::<AB>(4 + i as u64), v(s.c[i]), gate.clone() * v(s.a[i]));
            }
        };
        let emit_bytes =
            |b: &mut AB, em: &mut dyn FnMut(&mut AB, &AB::Expr, AB::Expr, AB::Expr, AB::Expr),
             msg: &AB::Expr,
             pos: AB::Expr,
             bytes: &[AB::Expr],
             gate: AB::Expr| {
                for (i, x) in bytes.iter().enumerate() {
                    em(b, msg, pos.clone() + k::<AB>(i as u64), x.clone(), gate.clone());
                }
            };
        let consts = |xs: &[u8]| -> Vec<AB::Expr> { xs.iter().map(|&x| k::<AB>(x as u64)).collect() };
        let tail = consts(&[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3]);
        let rid = vs(&c.rid);
        let pk = vs(&c.pk);
        // ---- K_RC: the receipt ----
        {
            let o = v(c.o);
            emit_str(b, &mut em, &rc_msg, o.clone(), &c.sp, lp.clone(), act.clone());
            let q1 = o + k::<AB>(4) + lp.clone();
            emit_str(b, &mut em, &rc_msg, q1.clone(), &c.sv, lv.clone(), act.clone());
            let q2 = q1 + k::<AB>(4) + lv.clone();
            emit_bytes(b, &mut em, &rc_msg, q2.clone(), &rid, act.clone());
            em(b, &rc_msg, q2.clone() + k::<AB>(32), z(), act.clone());
            emit_str(b, &mut em, &rc_msg, q2.clone() + k::<AB>(33), &c.ss, ls.clone(), act.clone());
            let q3 = q2 + k::<AB>(37) + ls.clone();
            em(b, &rc_msg, q3.clone(), kt.clone(), act.clone());
            emit_bytes(b, &mut em, &rc_msg, q3.clone() + one.clone(), &pk[..32], act.clone());
            emit_bytes(b, &mut em, &rc_msg, q3.clone() + k::<AB>(33), &pk[32..], act.clone() * kt.clone());
            let q4 = q3 + k::<AB>(33) + kt.clone() * k::<AB>(32);
            emit_bytes(b, &mut em, &rc_msg, q4.clone(), &gp, act.clone());
            emit_bytes(b, &mut em, &rc_msg, q4.clone() + k::<AB>(16), &tail, act.clone());
            emit_bytes(b, &mut em, &rc_msg, q4 + k::<AB>(29), &vs(&c.dep), act.clone());
        }
        // ---- K_PEO|r ----
        {
            em(b, &peo_msg, z(), hr.clone(), act.clone());
            emit_bytes(b, &mut em, &peo_msg, one.clone(), &consts(&[0, 0, 0]), act.clone());
            emit_bytes(b, &mut em, &peo_msg, k::<AB>(4), &vs(&c.refund_id), hr.clone());
            let u = k::<AB>(4) + hr.clone() * k::<AB>(32);
            emit_bytes(b, &mut em, &peo_msg, u.clone(), &consts(&G_LE8), act.clone());
            emit_bytes(b, &mut em, &peo_msg, u.clone() + k::<AB>(8), &burnt, act.clone());
            emit_str(b, &mut em, &peo_msg, u.clone() + k::<AB>(24), &c.sv, lv.clone(), act.clone());
            let w = u + k::<AB>(28) + lv.clone();
            emit_bytes(b, &mut em, &peo_msg, w, &consts(&[2, 0, 0, 0, 0]), act.clone());
        }
        // ---- K_LEAF|r ----
        emit_bytes(b, &mut em, &leaf_msg, z(), &consts(&[2, 0, 0, 0]), act.clone());
        emit_bytes(b, &mut em, &leaf_msg, k::<AB>(4), &rid, act.clone());
        emit_bytes(b, &mut em, &leaf_msg, k::<AB>(36), &vs(&c.peo_dig), act.clone());
        // ---- K_RID|r ----
        {
            emit_bytes(b, &mut em, &rid_msg, z(), &rid, hr.clone());
            let h: Vec<AB::Expr> = pvs[PV_HEIGHT..PV_HEIGHT + 8].to_vec();
            emit_bytes(b, &mut em, &rid_msg, k::<AB>(32), &h, hr.clone());
            emit_bytes(b, &mut em, &rid_msg, k::<AB>(40), &consts(&[0; 8]), hr.clone());
        }
        // ---- K_RF: the refund receipt ----
        {
            let o2 = v(c.o2);
            emit_bytes(b, &mut em, &rf_msg, o2.clone(), &consts(&[6, 0, 0, 0]), hr.clone());
            emit_bytes(b, &mut em, &rf_msg, o2.clone() + k::<AB>(4), &consts(SYSTEM), hr.clone());
            emit_str(b, &mut em, &rf_msg, o2.clone() + k::<AB>(10), &c.ss, ls.clone(), hr.clone());
            let x = o2 + k::<AB>(14) + ls.clone();
            emit_bytes(b, &mut em, &rf_msg, x.clone(), &vs(&c.refund_id), hr.clone());
            em(b, &rf_msg, x.clone() + k::<AB>(32), z(), hr.clone());
            emit_str(b, &mut em, &rf_msg, x.clone() + k::<AB>(33), &c.ss, ls.clone(), hr.clone());
            let y = x + k::<AB>(37) + ls.clone();
            em(b, &rf_msg, y.clone(), kt.clone(), hr.clone());
            emit_bytes(b, &mut em, &rf_msg, y.clone() + one.clone(), &pk[..32], hr.clone());
            emit_bytes(b, &mut em, &rf_msg, y.clone() + k::<AB>(33), &pk[32..], hr.clone() * kt.clone());
            let zz = y + k::<AB>(33) + kt.clone() * k::<AB>(32);
            emit_bytes(b, &mut em, &rf_msg, zz.clone(), &consts(&[0; 16]), hr.clone());
            emit_bytes(b, &mut em, &rf_msg, zz.clone() + k::<AB>(16), &tail, hr.clone());
            emit_bytes(b, &mut em, &rf_msg, zz + k::<AB>(29), &ramt, hr.clone());
        }
    }
}

/// `G` as a u64 little-endian (8 bytes), as it appears in the outcome.
pub const G_LE8: [u8; 8] = (crate::spec::G as u64).to_le_bytes();
