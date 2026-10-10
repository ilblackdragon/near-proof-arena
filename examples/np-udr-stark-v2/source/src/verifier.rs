//! Reference verifier for `np-udr-stark-v1` (FORMATS.md v1) and `-v2`
//! (FORMATS.md §8: public segments, `auxGroup ∈ {1,2,3}`), written to be read
//! side by side with L4's `ZkFormal.Stark.{Bcs,Protocol,Verifier}` and
//! `ZkFormal.V2.{Air,Verifier}`.
//! It is NOT part of the soundness argument; it pins the protocol down in
//! Rust so the prover can be tested without the Lean toolchain.

use p3_field::{Field, PrimeCharacteristicRing};

use crate::air::{Air, Tape};
use crate::aux::{AuxLayout, aux_constraints};
use crate::field::{EF, F, ef_from_base, ef_from_coeffs, omega, put_ef};
use crate::mmcs::{self, index_sets};
use crate::protocol::{
    NUM_CHUNKS, PER_CHUNK, Proof, Schedule, batch_coeffs, oracle_shapes, parse_openings,
    parse_prefix, point,
};
use crate::transcript::Transcript;

/// Public inputs: `pub i = cb[i]` (as a field element); 0 beyond `|cb|`.
pub fn public_inputs(air: &Air, cb: &[u8]) -> Vec<F> {
    (0..air.num_pub.max(cb.len()))
        .map(|i| F::new(*cb.get(i).unwrap_or(&0) as u32))
        .collect()
}

/// Little-endian u32 over `cb[at..at+4]`, 0 past the claim (`leNat` of `pub.getD`).
fn le_u32(cb: &[u8], at: usize) -> usize {
    (0..4)
        .map(|k| (*cb.get(at.saturating_add(k)).unwrap_or(&0) as usize) << (8 * k))
        .sum()
}

impl crate::air::PubSeg {
    /// `PubSeg.count`.
    pub fn count(&self, cb: &[u8]) -> usize {
        le_u32(cb, self.count_at)
    }
    /// `PubSeg.startOffset`.
    pub fn start_offset(&self, cb: &[u8]) -> usize {
        self.start_at.map_or(self.start, |a| le_u32(cb, a))
    }
    /// `PubSeg.fits`: `start + count·width ≤ min(|cb|, maxPub)` (no overflow: all
    /// three terms are < 2^32 and `width` is a static constant).
    pub fn fits(&self, max_pub: usize, cb: &[u8]) -> bool {
        let end = self.start_offset(cb) as u128 + self.count(cb) as u128 * self.width as u128;
        end <= cb.len() as u128 && end <= max_pub as u128
    }
    /// `PubSeg.record j` (only meaningful when the segment fits).
    pub fn record(&self, cb: &[u8], j: usize) -> Vec<F> {
        let base = self.start_offset(cb) + j * self.width;
        self.prefix
            .iter()
            .map(|&n| F::from_u64(n))
            .chain(self.index_base.map(|b| F::from_u64(b + j as u64)))
            .chain((0..self.width).map(|c| F::new(*cb.get(base + c).unwrap_or(&0) as u32)))
            .collect()
    }
}

/// `pubFit`: every public segment fits.
pub fn pub_fit(air: &Air, cb: &[u8]) -> bool {
    air.pub_segs.iter().all(|sg| sg.fits(air.max_pub, cb))
}

/// `pubMsgs`: all public messages `(bus, send, record)`, segment by segment.
/// Call only after `pub_fit` (the counts are then bounded by `|cb|`).
pub fn pub_msgs(air: &Air, cb: &[u8]) -> Vec<(usize, bool, Vec<F>)> {
    air.pub_segs
        .iter()
        .flat_map(|sg| (0..sg.count(cb)).map(move |j| (sg.bus, sg.send, sg.record(cb, j))))
        .collect()
}

/// `pubProd s`: `∏ (γ − fp(m ‖ (bus+1)))` over the public messages of side `s`.
pub fn pub_prod(msgs: &[(usize, bool, Vec<F>)], alpha: EF, gamma: EF, send: bool) -> EF {
    msgs.iter()
        .filter(|m| m.1 == send)
        .fold(EF::ONE, |acc, (b, _, m)| {
            let me: Vec<EF> = m.iter().map(|&x| EF::from(x)).collect();
            acc * (gamma - crate::aux::fingerprint(*b, &me, alpha))
        })
}

/// All Fiat–Shamir challenges of one proof.
#[derive(Clone, Debug)]
pub struct Challenges {
    pub alpha_fp: EF,
    pub gamma_mul: EF,
    pub alpha_c: EF,
    pub z: EF,
    /// the shared batching vector `r_1..r_L`
    pub batch: Vec<EF>,
    pub beta: Vec<EF>,
    /// roll-in challenge per FRI layer (zero where none)
    pub gamma_roll: Vec<EF>,
    pub queries: Vec<usize>,
}

pub fn efs_bytes(xs: &[EF]) -> Vec<u8> {
    let mut b = vec![];
    for x in xs {
        put_ef(&mut b, *x);
    }
    b
}

pub fn aux_msg(root_aux: &[u8; 64], finals: &[EF]) -> Vec<u8> {
    let mut b = root_aux.to_vec();
    b.extend(efs_bytes(finals));
    b
}

/// Zerofier and the selectors `[first, last, transition]` at `x`, for a trace of
/// `2^h` rows: `first = Z/(T(x−1))`, `last = Z/(T(ωx−1))`.
pub fn selectors(x: EF, h: usize) -> (EF, [EF; 3]) {
    let t = ef_from_base(F::from_u64(1 << h));
    let zh = x.exp_power_of_2(h) - EF::ONE;
    let w = ef_from_base(omega(h));
    let first = zh * (t * (x - EF::ONE)).inverse();
    let last = zh * (t * (w * x - EF::ONE)).inverse();
    (zh, [first, last, EF::ONE - last])
}

/// Offsets of each table's OOD values.
pub fn ood_offsets(sch: &Schedule) -> Vec<usize> {
    let mut v = vec![];
    let mut o = 0;
    for t in 0..sch.num_tables() {
        v.push(o);
        o += sch.ood_len(t);
    }
    v
}

pub fn verify(air: &Air, pub_tape: &[u8], cb: &[u8], bytes: &[u8]) -> Result<(), String> {
    let (mut proof, sch, rest) = parse_prefix(air, bytes).ok_or("parse (commit phase)")?;
    let mut tr = Transcript::new(pub_tape, cb);
    let ch = replay(&sch, &mut tr, &proof);
    parse_openings(&mut proof, &sch, &ch.queries, rest).ok_or("parse (openings)")?;
    verify_parsed(air, cb, &sch, &proof, &ch)
}

pub fn verify_parsed(
    air: &Air,
    cb: &[u8],
    sch: &Schedule,
    proof: &Proof,
    ch: &Challenges,
) -> Result<(), String> {
    let pubs = public_inputs(air, cb);
    // `okLens && pubFit AP pub && globalChecksP …` (okLens is enforced by the parser)
    if !pub_fit(air, cb) {
        return Err("public segment does not fit (pubFit)".into());
    }
    let pmsgs = pub_msgs(air, cb);
    global_checks(air, sch, &proof.ood, &proof.aux_finals, ch, &pubs, &pmsgs)?;
    let ood_off = ood_offsets(sch);
    let nt = sch.num_tables();
    let l0 = sch.l0;
    let qs = &ch.queries;

    // ---- MMCS openings ----
    let roots: Vec<&[u8; 64]> = [&proof.root_main, &proof.root_aux, &proof.root_quot]
        .into_iter()
        .chain(proof.fri_roots.iter())
        .collect();
    for (i, ((shape, sh), op)) in oracle_shapes(sch).iter().zip(proof.openings()).enumerate() {
        let idx: Vec<usize> = qs.iter().map(|&x| x >> sh).collect();
        let shp: Vec<(usize, usize)> = shape.iter().map(|&(l, w)| (w, l)).collect();
        if !mmcs::verify(&shp, roots[i], &idx, op) {
            return Err(format!("opening {i}"));
        }
    }
    let sets = index_sets(l0, qs);
    let coeffs: Vec<Vec<EF>> = (0..sch.class_layers.len())
        .map(|ci| batch_coeffs(&ch.batch, sch.batch_len[ci]))
        .collect();

    // batched DEEP value of class layer `ci` at layer-c position j (= x >> c)
    let deep = |ci: usize, j: usize| -> EF {
        let c = sch.class_layers[ci];
        let x = ef_from_base(point(l0, c, j));
        let p = sets[c].binary_search(&j).unwrap();
        let mut acc = EF::ZERO;
        let mut i = 0;
        for t in sch.tables_of(c) {
            let gz = ch.z * ef_from_base(omega(sch.heights[t]));
            let inv_z = (x - ch.z).inverse();
            let inv_gz = (x - gz).inverse();
            let v = &proof.ood[ood_off[t]..ood_off[t] + sch.ood_len(t)];
            let w = sch.w_main[t];
            let wa = sch.w_aux[t];
            let nq = sch.n_quot[t];
            let main = &proof.open_main.rows[t][p * w..(p + 1) * w];
            let aux = &proof.open_aux.rows[t][p * 8 * wa..(p + 1) * 8 * wa];
            let quot = &proof.open_quot.rows[t][p * 8 * nq..(p + 1) * 8 * nq];
            let mut k = 0;
            let mut term = |fx: EF, inv: EF| {
                acc += coeffs[ci][i] * (fx - v[k]) * inv;
                i += 1;
                k += 1;
            };
            for col in 0..w {
                term(ef_from_base(main[col]), inv_z);
            }
            for col in 0..w {
                term(ef_from_base(main[col]), inv_gz);
            }
            for col in 0..wa {
                term(ef_from_coeffs(&aux[8 * col..8 * col + 8]), inv_z);
            }
            for col in 0..wa {
                term(ef_from_coeffs(&aux[8 * col..8 * col + 8]), inv_gz);
            }
            for col in 0..nq {
                term(ef_from_coeffs(&quot[8 * col..8 * col + 8]), inv_z);
            }
        }
        acc
    };
    let roll = |k: usize, x: usize, v: EF| -> EF {
        match sch.class_layers.iter().position(|&cl| cl == k) {
            Some(ci) if k > 0 => v + ch.gamma_roll[k] * deep(ci, x >> k),
            _ => v,
        }
    };

    let two_inv = F::TWO.inverse();
    let _ = nt;
    for &x in qs {
        let mut val = deep(0, x);
        for (i, &(c, a)) in sch.committed.iter().enumerate() {
            val = roll(c, x, val);
            let pos = x >> c;
            let leaf = pos >> a;
            let mut s: Vec<usize> = qs.iter().map(|&q| q >> (c + a)).collect();
            s.sort_unstable();
            s.dedup();
            let p = s.binary_search(&leaf).unwrap();
            let w = 8 << a;
            let row = &proof.open_fri[i].rows[0][p * w..(p + 1) * w];
            let mut arr: Vec<EF> = (0..1 << a)
                .map(|u| ef_from_coeffs(&row[8 * u..8 * u + 8]))
                .collect();
            if arr[pos & ((1 << a) - 1)] != val {
                return Err(format!("fri layer {c} value mismatch"));
            }
            let mut base = leaf << a;
            for s in 0..a {
                let layer = c + s;
                let half = arr.len() / 2;
                let mut nxt = Vec::with_capacity(half);
                for u in 0..half {
                    let y = point(l0, layer, base + 2 * u);
                    let (e0, e1) = (arr[2 * u], arr[2 * u + 1]);
                    nxt.push(
                        (e0 + e1) * two_inv + ch.beta[layer] * (e0 - e1) * (F::TWO * y).inverse(),
                    );
                }
                arr = nxt;
                base >>= 1;
            }
            val = arr[0];
        }
        val = roll(sch.fri_l, x, val);
        let y = ef_from_base(point(l0, sch.fri_l, x >> sch.fri_l));
        if val != proof.final_poly[0] + proof.final_poly[1] * y {
            return Err("final polynomial mismatch".into());
        }
    }
    Ok(())
}

/// Run all rounds of the transcript against the proof's messages
/// (FORMATS.md §4).
pub fn replay(sch: &Schedule, tr: &mut Transcript, proof: &Proof) -> Challenges {
    tr.absorb(&[proof.root_main], &sch.header_bytes());
    let alpha_fp = tr.chal();
    let gamma_mul = tr.chal();
    tr.absorb(&[proof.root_aux], &efs_bytes(&proof.aux_finals));
    let alpha_c = tr.chal();
    tr.absorb(&[proof.root_quot], &[]);
    let z = tr.chal_ood();
    tr.absorb(&[], &efs_bytes(&proof.ood));
    let batch: Vec<EF> = (0..sch.batch_rounds).map(|_| tr.chal()).collect();
    let mut beta = vec![];
    let mut gamma_roll = vec![EF::ZERO; sch.fri_l + 1];
    for k in 0..sch.fri_l {
        if k > 0 && sch.class_layers.contains(&k) {
            gamma_roll[k] = tr.chal();
        }
        if let Some(i) = sch.committed_at(k) {
            tr.absorb(&[proof.fri_roots[i]], &[]);
        }
        beta.push(tr.chal());
    }
    if sch.fri_l > 0 && sch.class_layers.contains(&sch.fri_l) {
        gamma_roll[sch.fri_l] = tr.chal();
    }
    tr.absorb(&[], &efs_bytes(&proof.final_poly));
    let queries = tr.finish_queries(sch.l0, NUM_CHUNKS, PER_CHUNK);
    Challenges {
        alpha_fp,
        gamma_mul,
        alpha_c,
        z,
        batch,
        beta,
        gamma_roll,
        queries,
    }
}

/// ALI identity of every table at `z` (with the aux constraints) and the
/// bus equation `∏ send finals · Π_pub(true) = ∏ receive finals · Π_pub(false)`
/// (`globalChecksP`; with no public segments this is v1's).
#[allow(clippy::too_many_arguments)]
pub fn global_checks(
    air: &Air,
    sch: &Schedule,
    ood: &[EF],
    finals: &[EF],
    ch: &Challenges,
    pubs: &[F],
    pmsgs: &[(usize, bool, Vec<F>)],
) -> Result<(), String> {
    let mut off = 0;
    let mut foff = 0;
    let (mut sends, mut recvs) = (EF::ONE, EF::ONE);
    for t in 0..sch.num_tables() {
        let tab = &air.tables[t];
        let lay = AuxLayout::new(tab, air.aux_group);
        let w = sch.w_main[t];
        let wa = sch.w_aux[t];
        let v = &ood[off..off + sch.ood_len(t)];
        let fins = &finals[foff..foff + sch.n_finals[t]];
        for (g, f) in fins.iter().enumerate() {
            if g < lay.send_groups {
                sends *= *f;
            } else {
                recvs *= *f;
            }
        }
        let (zh, sel) = selectors(ch.z, sch.heights[t]);
        let col = |c: usize, n: bool| if n { v[w + c] } else { v[c] };
        let tape = Tape::compile(&tab.constraints);
        let mut regs = vec![];
        tape.eval::<EF>(&mut regs, col, pubs, sel);
        let mut cs: Vec<EF> = tape.outputs.iter().map(|&o| regs[o as usize]).collect();
        let mut iregs = vec![];
        lay.itape.eval::<EF>(&mut iregs, col, pubs, sel);
        let ivals: Vec<EF> = lay
            .itape
            .outputs
            .iter()
            .map(|&o| iregs[o as usize])
            .collect();
        let aux = &v[2 * w..2 * w + wa];
        let aux_n = &v[2 * w + wa..2 * w + 2 * wa];
        let mut phis = vec![];
        aux_constraints(
            tab,
            &lay,
            &ivals,
            ch.alpha_fp,
            ch.gamma_mul,
            aux,
            aux_n,
            fins,
            sel,
            &mut cs,
            &mut phis,
        );
        let mut acc = EF::ZERO;
        let mut ap = EF::ONE;
        for c in &cs {
            acc += ap * *c;
            ap *= ch.alpha_c;
        }
        let qoff = 2 * w + 2 * wa;
        let zt = ch.z.exp_power_of_2(sch.heights[t]);
        let mut q = EF::ZERO;
        let mut zp = EF::ONE;
        for j in 0..sch.n_quot[t] {
            q += zp * v[qoff + j];
            zp *= zt;
        }
        if acc != zh * q {
            return Err(format!("ALI identity fails for table {t}"));
        }
        off += sch.ood_len(t);
        foff += sch.n_finals[t];
    }
    sends *= pub_prod(pmsgs, ch.alpha_fp, ch.gamma_mul, true);
    recvs *= pub_prod(pmsgs, ch.alpha_fp, ch.gamma_mul, false);
    if sends != recvs {
        return Err("bus products differ".into());
    }
    Ok(())
}
