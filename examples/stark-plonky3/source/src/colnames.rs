//! Human-readable column names per table (for the witness-mutation report).

use crate::air::NpAir;
use p3_air::BaseAir;
use p3_sha256_air::NUM_SHA256_COLS;

struct N(Vec<String>);
impl N {
    fn one(&mut self, c: usize, n: &str) {
        self.0[c] = n.to_string();
    }
    fn arr(&mut self, cs: &[usize], n: &str) {
        for (i, &c) in cs.iter().enumerate() {
            self.0[c] = format!("{n}[{i}]");
        }
    }
}

pub fn names(air: &NpAir) -> Vec<String> {
    let w = BaseAir::<crate::config::Val>::width(air);
    let mut n = N(vec![String::new(); w]);
    match air {
        NpAir::Sha(a) => {
            let c = &a.c;
            // Sha256Cols layout (Plonky3 sha256-air columns.rs)
            let mut off = 0;
            let mut grp = |name: &str, len: usize, n: &mut N| {
                for i in 0..len {
                    n.0[off + i] = format!("sha.{name}[{i}]");
                }
                off += len;
            };
            grp("h_in", 16, &mut n);
            grp("a_chain", 68 * 32, &mut n);
            grp("e_chain", 68 * 32, &mut n);
            grp("w", 64 * 32, &mut n);
            grp("sched_sigma0", 96, &mut n);
            grp("sched_sigma1", 96, &mut n);
            grp("sched_tmp", 96, &mut n);
            grp("rounds", 64 * 12, &mut n);
            grp("h_out", 256, &mut n);
            assert_eq!(off, NUM_SHA256_COLS);
            for (cc, nm) in [
                (c.act, "act"),
                (c.first, "first"),
                (c.last, "last"),
                (c.msg, "msg"),
                (c.blk, "blk"),
                (c.cnt, "cnt"),
                (c.seen, "seen"),
                (c.p80, "p80"),
                (c.pn, "pn"),
                (c.dm, "dm(mult)"),
            ] {
                n.one(cc, nm);
            }
            n.arr(&c.f, "f");
        }
        NpAir::Rcpt(a) => {
            let c = &*a.c;
            for (cc, nm) in [
                (c.act, "act"),
                (c.isf, "isf"),
                (c.lastr, "lastr"),
                (c.r, "r"),
                (c.o, "o"),
                (c.o2, "o2"),
                (c.hexcnt, "hexcnt"),
                (c.hexcnt2, "hexcnt2"),
                (c.inv_sys, "inv_sys"),
                (c.kt, "kt"),
                (c.hr, "hr"),
                (c.dinv, "dinv"),
                (c.rf, "rf"),
                (c.kacc, "kacc"),
                (c.t_prev, "t_prev"),
                (c.inv_max, "inv_max"),
                (c.sz, "sz"),
                (c.m_leaf, "m_leaf(mult)"),
            ] {
                n.one(cc, nm);
            }
            n.arr(&c.inv_n, "inv_n");
            for (s, p) in [(&c.sp, "pred"), (&c.sv, "recv"), (&c.ss, "signer")] {
                n.arr(&s.a, &format!("{p}.a"));
                n.arr(&s.c, &format!("{p}.c"));
                n.arr(&s.cls, &format!("{p}.cls"));
            }
            for (v, nm) in [
                (&c.rid, "rid"),
                (&c.pk, "pk"),
                (&c.gp, "gp"),
                (&c.dep, "dep"),
                (&c.d, "d"),
                (&c.cd, "cd"),
                (&c.burnt, "burnt"),
                (&c.cb, "cb"),
                (&c.ramt, "ramt"),
                (&c.cr, "cr"),
                (&c.t, "tok"),
                (&c.ct, "ct"),
                (&c.refund_id, "refund_id"),
                (&c.peo_dig, "peo_dig"),
                (&c.locked, "locked"),
                (&c.storage, "storage"),
                (&c.abef, "abef"),
                (&c.aaft, "aaft"),
                (&c.ca, "ca"),
                (&c.tot, "tot"),
                (&c.ctot, "ctot"),
                (&c.q, "q"),
                (&c.cq, "cq"),
                (&c.e, "e"),
                (&c.ce, "ce"),
            ] {
                n.arr(v, nm);
            }
        }
        NpAir::Mrk(a) => {
            let c = &*a.c;
            for (cc, nm) in [
                (c.act, "act"),
                (c.isf, "isf"),
                (c.j, "j"),
                (c.i, "i"),
                (c.sp, "sp"),
                (c.s, "s"),
                (c.odd, "odd"),
                (c.lil, "lil"),
                (c.root, "root"),
                (c.rinv, "rinv"),
                (c.idx, "idx"),
                (c.msg_l, "msg_l"),
                (c.msg_r, "msg_r"),
                (c.own, "own"),
                (c.m_prov, "m_prov(mult)"),
            ] {
                n.one(cc, nm);
            }
            n.arr(&c.l, "l");
            n.arr(&c.rr, "r");
        }
        NpAir::Sort(a) => {
            let c = &*a.c;
            n.one(c.act, "act");
            n.one(c.isf, "isf");
            n.arr(&c.rid, "rid");
            n.arr(&c.diff, "diff");
            n.arr(&c.cs, "cs");
        }
        NpAir::Acct(a) => {
            let c = &*a.c;
            for (cc, nm) in [
                (c.act, "act"),
                (c.isf, "isf"),
                (c.k, "k"),
                (c.o, "owner"),
                (c.io, "iterm"),
                (c.t_last, "t_last"),
                (c.m_acct, "m_acct(mult)"),
                (c.inv_max, "inv_max"),
            ] {
                n.one(cc, nm);
            }
            n.arr(&c.a, "a");
            n.arr(&c.c, "c");
            n.arr(&c.hi, "hi");
            n.arr(&c.lo, "lo");
            n.arr(&c.val, "val");
            n.arr(&c.post, "post");
        }
        NpAir::Node(a) => {
            let c = &*a.c;
            for (cc, nm) in [
                (c.act, "act"),
                (c.isf, "isf"),
                (c.lastn, "lastn"),
                (c.nid, "nid"),
                (c.tl, "tl"),
                (c.te, "te"),
                (c.tb1, "tb1"),
                (c.tb2, "tb2"),
                (c.odd, "odd"),
                (c.x0, "x0"),
                (c.tv, "tv"),
                (c.vk, "vk"),
                (c.m_nib, "m_nib(mult)"),
                (c.m_eps, "m_eps(mult)"),
                (c.pv_, "p_vref"),
                (c.pc, "p_children"),
                (c.pm, "p_mem"),
                (c.s, "s"),
                (c.ssum, "ssum"),
            ] {
                n.one(cc, nm);
            }
            for (v, nm) in [
                (&c.kb, "kb"),
                (&c.khi, "khi"),
                (&c.klo, "klo"),
                (&c.vlen, "vlen"),
                (&c.vh, "vh"),
                (&c.pvh, "pvh"),
                (&c.bm, "bm"),
                (&c.rv, "rv"),
                (&c.cid, "cid"),
                (&c.me, "me(mult)"),
                (&c.mem, "mem"),
                (&c.wsd, "wsd"),
            ] {
                n.arr(v, nm);
            }
            for j in 0..16 {
                n.arr(&c.w[j], &format!("w{j}"));
                n.arr(&c.pw[j], &format!("pw{j}"));
            }
        }
        NpAir::Path(a) => {
            let c = &*a.c;
            for (cc, nm) in [
                (c.act, "act"),
                (c.isf, "isf"),
                (c.start, "start"),
                (c.end, "end"),
                (c.k, "k"),
                (c.t, "t"),
                (c.nib, "nib"),
                (c.n, "n"),
                (c.i, "i"),
                (c.n2, "n2"),
                (c.i2, "i2"),
                (c.jump, "jump"),
                (c.n3, "n3"),
                (c.i3, "i3"),
            ] {
                n.one(cc, nm);
            }
        }
        NpAir::Byte(_) => {
            n.0 = vec!["m_range8(mult)".into(), "m_class(mult)".into(), "m_nib(mult)".into()];
        }
        NpAir::R12(_) => n.0 = vec!["m_range12(mult)".into()],
    }
    for (i, s) in n.0.iter().enumerate() {
        assert!(!s.is_empty(), "{}: unnamed column {i}", air.name());
    }
    n.0
}

/// Provider-multiplicity columns: free by design (the prover chooses them;
/// LogUp soundness does not depend on them).
pub fn is_multiplicity(name: &str) -> bool {
    name.contains("(mult)")
}
