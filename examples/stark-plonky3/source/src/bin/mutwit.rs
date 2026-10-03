//! Witness-mutation (under-constraint) probe.
//!
//! `mutwit [--rows R] [--seed S] CASE_DIR...`
//!
//! For each case: build the honest traces, then for every column of every
//! table and up to R sampled active rows (+1 padding row), add 1 to that
//! single cell and decide whether the proof system would still accept the
//! mutated witness, i.e. whether
//!   (a) some AIR constraint of the affected rows (r-1, r) is nonzero, or
//!   (b) some permutation bus no longer balances, or
//!   (c) some lookup query has no table entry left (provider multiplicities
//!       are re-chosen by the attacker, so they are never counted as kills;
//!       multiplicity columns are skipped).
//! A mutant passing all three is UNDETECTED and listed for triage.
//!
//! This is bounded testing of single-cell perturbations, not a proof of
//! full constraint coverage.
use npstark::air::{NpAir, all_airs};
use npstark::config::Val;
use npstark::consts::LOOKUP_BUSES;
use npstark::eval::{RowEval, eval_pair, eval_row, key, Key};
use p3_air::BaseAir;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;
use std::collections::{BTreeMap, HashMap};

#[derive(Default, Clone, Copy)]
struct Stat {
    tried: usize,
    by_constraint: usize,
    by_perm: usize,
    by_lookup: usize,
    undetected_active: usize,
    undetected_padding: usize,
}

fn act_col(air: &NpAir) -> Option<usize> {
    match air {
        NpAir::Sha(a) => Some(a.c.act),
        NpAir::Rcpt(a) => Some(a.c.act),
        NpAir::Mrk(a) => Some(a.c.act),
        NpAir::Sort(a) => Some(a.c.act),
        NpAir::Acct(a) => Some(a.c.act),
        NpAir::Node(a) => Some(a.c.act),
        NpAir::Path(a) => Some(a.c.act),
        _ => None,
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let mut nrows = 2usize;
    let mut seed = 7u64;
    let mut cases = vec![];
    while let Some(a) = args.next() {
        match a.as_str() {
            "--rows" => nrows = args.next().unwrap().parse().unwrap(),
            "--seed" => seed = args.next().unwrap().parse().unwrap(),
            _ => cases.push(std::path::PathBuf::from(a)),
        }
    }
    let airs = all_airs();
    let mut total: BTreeMap<&'static str, Stat> = BTreeMap::new();
    let mut undetected: BTreeMap<(String, String, bool), usize> = BTreeMap::new();
    for d in &cases {
        let req = std::fs::read(d.join("request.bin")).unwrap();
        let witb = std::fs::read(d.join("witness.bin")).unwrap();
        let wit = npstark::witness::build(&req, &witb).unwrap();
        let mut traces = npstark::trace::all_traces(&airs, &wit);
        let pvs = npstark::trace::pv_vals(&wit.pv);
        npstark::trace::fill_multiplicities(&airs, &mut traces, &pvs);
        let pres: Vec<Option<RowMajorMatrix<Val>>> =
            airs.iter().map(|a| BaseAir::<Val>::preprocessed_trace(a)).collect();
        // honest evaluations
        let evals: Vec<Vec<RowEval>> = airs
            .iter()
            .zip(traces.iter())
            .zip(pres.iter())
            .map(|((a, t), p)| {
                let pv: &[Val] = if a.num_pv() > 0 { &pvs } else { &[] };
                (0..t.height()).into_par_iter().map(|r| eval_row(a, t, p.as_ref(), pv, r, true)).collect()
            })
            .collect();
        let mut provided: HashMap<Key, i64> = HashMap::new();
        let mut queries: HashMap<Key, i64> = HashMap::new();
        for ev in &evals {
            for e in ev {
                assert!(e.failed.is_empty(), "honest trace violates constraints");
                for (bus, t, c, w) in &e.inter {
                    if LOOKUP_BUSES.contains(bus) {
                        if *w == 0 {
                            *provided.entry(key(bus, t)).or_insert(0) += 1;
                        } else {
                            *queries.entry(key(bus, t)).or_insert(0) += c.as_canonical_u32() as i64;
                        }
                    }
                }
            }
        }
        for (ti, air) in airs.iter().enumerate() {
            if matches!(air, NpAir::Byte(_) | NpAir::R12(_)) {
                continue;
            }
            let names = npstark::colnames::names(air);
            let t = &traces[ti];
            let (h, w) = (t.height(), t.width());
            let ac = act_col(air).unwrap();
            let active: Vec<usize> = (0..h).filter(|&r| t.values[r * w + ac] == Val::ONE).collect();
            let padding: Vec<usize> = (0..h).filter(|&r| t.values[r * w + ac] != Val::ONE).collect();
            let pv: &[Val] = if air.num_pv() > 0 { &pvs } else { &[] };
            let mut rng = seed ^ (ti as u64) << 32;
            let mut next = || {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                rng
            };
            let mut jobs: Vec<(usize, usize, bool)> = vec![];
            for c in 0..w {
                if npstark::colnames::is_multiplicity(&names[c]) {
                    continue;
                }
                for _ in 0..nrows.min(active.len()) {
                    jobs.push((c, active[(next() % active.len() as u64) as usize], true));
                }
                if !padding.is_empty() {
                    jobs.push((c, padding[(next() % padding.len() as u64) as usize], false));
                }
            }
            let res: Vec<(usize, bool, u8)> = jobs
                .par_iter()
                .map(|&(c, r, act)| {
                    let mut rows_new: Vec<Vec<Val>> = vec![];
                    let affected: Vec<usize> = if r > 0 { vec![r - 1, r] } else { vec![r] };
                    let mut cur_r = t.values[r * w..(r + 1) * w].to_vec();
                    cur_r[c] += Val::ONE;
                    let mut kind = 0u8; // 0 undetected, 1 constraint, 2 perm, 3 lookup
                    let mut delta: HashMap<Key, i64> = HashMap::new();
                    let mut prov_delta: HashMap<Key, i64> = HashMap::new();
                    for &ar in &affected {
                        let nr = (ar + 1) % h;
                        let cur: Vec<Val> =
                            if ar == r { cur_r.clone() } else { t.values[ar * w..(ar + 1) * w].to_vec() };
                        let nxt: Vec<Val> =
                            if nr == r { cur_r.clone() } else { t.values[nr * w..(nr + 1) * w].to_vec() };
                        let (pc, pn): (Vec<Val>, Vec<Val>) = match &pres[ti] {
                            Some(p) => {
                                let pw = p.width();
                                (p.values[ar * pw..(ar + 1) * pw].to_vec(), p.values[nr * pw..(nr + 1) * pw].to_vec())
                            }
                            None => (vec![], vec![]),
                        };
                        let e = eval_pair(air, &cur, &nxt, &pc, &pn, pv, ar == 0, ar + 1 == h, true);
                        if !e.failed.is_empty() {
                            kind = 1;
                        }
                        let old = &evals[ti][ar];
                        for (sign, ints) in [(1i64, &e.inter), (-1i64, &old.inter)] {
                            for (bus, tup, cnt, wt) in ints {
                                let k = key(bus, tup);
                                if LOOKUP_BUSES.contains(bus) && *wt == 0 {
                                    *prov_delta.entry(k).or_insert(0) += sign;
                                } else {
                                    let cu = cnt.as_canonical_u32();
                                    let sc = if cu > Val::ORDER_U32 / 2 {
                                        -((Val::ORDER_U32 - cu) as i64)
                                    } else {
                                        cu as i64
                                    };
                                    *delta.entry(k).or_insert(0) += sign * sc;
                                }
                            }
                        }
                        rows_new.push(cur);
                    }
                    if kind == 0 {
                        for (k, dv) in &delta {
                            if *dv == 0 {
                                continue;
                            }
                            if !LOOKUP_BUSES.contains(&k.0) {
                                kind = 2;
                                break;
                            }
                        }
                    }
                    if kind == 0 {
                        // lookups: every queried tuple must still have an entry
                        let mut keys: Vec<&Key> = delta.keys().chain(prov_delta.keys()).collect();
                        keys.sort();
                        keys.dedup();
                        for k in keys {
                            if !LOOKUP_BUSES.contains(&k.0) {
                                continue;
                            }
                            let q = queries.get(k).copied().unwrap_or(0) + delta.get(k).copied().unwrap_or(0);
                            let p = provided.get(k).copied().unwrap_or(0) + prov_delta.get(k).copied().unwrap_or(0);
                            if q > 0 && p <= 0 {
                                kind = 3;
                                break;
                            }
                        }
                    }
                    (c, act, kind)
                })
                .collect();
            let st = total.entry(air.name()).or_default();
            for (c, act, kind) in res {
                st.tried += 1;
                match kind {
                    1 => st.by_constraint += 1,
                    2 => st.by_perm += 1,
                    3 => st.by_lookup += 1,
                    _ => {
                        if act {
                            st.undetected_active += 1;
                        } else {
                            st.undetected_padding += 1;
                        }
                        *undetected.entry((air.name().to_string(), names[c].clone(), act)).or_insert(0) += 1;
                    }
                }
            }
        }
        eprintln!("{}: done", d.display());
    }
    println!("table  tried  constraint  perm-bus  lookup  UNDETECTED(active)  undetected(padding)");
    for (n, s) in &total {
        println!(
            "{n:5} {:7} {:10} {:9} {:7} {:19} {:20}",
            s.tried, s.by_constraint, s.by_perm, s.by_lookup, s.undetected_active, s.undetected_padding
        );
    }
    println!("\nundetected single-cell mutations (table, column, row kind, count):");
    for ((t, c, act), n) in &undetected {
        println!("  {t:5} {c:24} {} x{n}", if *act { "ACTIVE " } else { "padding" });
    }
}
