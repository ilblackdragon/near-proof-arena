//! Reference verifier for `np-udr-stark-v1`, written to be read side by side
//! with the Lean verifier (L4). It is NOT part of the soundness argument; it
//! documents the protocol precisely and lets the prover be tested in Rust.

use p3_field::{Field, PrimeCharacteristicRing};

use crate::air::{Air, Tape};
use crate::field::{ef_from_base, ef_from_coeffs, omega, put_ef, EF, F};
use crate::hash::Digest32;
use crate::mmcs::{self, index_sets, Shape};
use crate::protocol::{batch_coeffs, point, Proof, Schedule, NUM_CHUNKS, PER_CHUNK, VERSION};
use crate::transcript::Transcript;

/// Public inputs: `pub i = cb[i]` (as a field element) for `i < |cb|`, else 0.
pub fn public_inputs(air: &Air, cb: &[u8]) -> Vec<F> {
    (0..air.num_pub).map(|i| F::new(*cb.get(i).unwrap_or(&0) as u32)).collect()
}

/// All Fiat–Shamir challenges of one proof.
#[derive(Clone, Debug)]
pub struct Challenges {
    pub alpha_fp: EF,
    pub gamma_mul: EF,
    pub alpha_c: EF,
    pub z: EF,
    /// per class layer, the batching challenges
    pub batch: Vec<Vec<EF>>,
    pub beta: Vec<EF>,
    /// roll-in challenge per FRI layer (zero where none)
    pub gamma_roll: Vec<EF>,
    pub queries: Vec<usize>,
}

/// Replays the transcript (shared by prover and verifier).
pub fn ood_bytes(ood: &[EF]) -> Vec<u8> {
    let mut b = vec![];
    for x in ood {
        put_ef(&mut b, *x);
    }
    b
}

pub fn aux_msg(root_aux: &[u8; 64], finals: &[EF]) -> Vec<u8> {
    let mut b = root_aux.to_vec();
    for x in finals {
        put_ef(&mut b, *x);
    }
    b
}

pub fn final_bytes(p: &[EF; 2]) -> Vec<u8> {
    ood_bytes(p)
}

/// Zerofier and the three selectors at `x`, for a trace of `2^h` rows.
pub fn selectors(x: EF, h: usize) -> (EF, [EF; 3]) {
    let t = F::from_u64(1 << h);
    let zh = x.exp_power_of_2(h) - EF::ONE;
    let g_inv = omega(h).inverse();
    let first = zh * (ef_from_base(t) * (x - EF::ONE)).inverse();
    let last = zh * ef_from_base(g_inv) * (ef_from_base(t) * (x - ef_from_base(g_inv))).inverse();
    (zh, [first, last, EF::ONE - last])
}

pub fn verify(air: &Air, pub_digest: &Digest32, cb: &[u8], bytes: &[u8]) -> Result<(), String> {
    let proof = Proof::from_bytes(bytes).ok_or("parse")?;
    verify_proof(air, pub_digest, cb, &proof)
}

pub fn verify_proof(air: &Air, pub_digest: &Digest32, cb: &[u8], proof: &Proof) -> Result<(), String> {
    if proof.version != VERSION {
        return Err("version".into());
    }
    let sch = Schedule::new(air, &proof.heights)?;
    let nt = sch.num_tables();
    if !proof.aux_finals.is_empty() {
        return Err("aux finals count".into());
    }
    if proof.ood.len() != sch.num_ood() {
        return Err("ood count".into());
    }
    if proof.fri_roots.len() != sch.committed.len() || proof.open_fri.len() != sch.committed.len() {
        return Err("fri layer count".into());
    }

    // ---- transcript ----
    let mut tr = Transcript::new(pub_digest, &sch.header_bytes(), cb);
    let ch = replay(&sch, &mut tr, proof);

    // ---- ALI identity at z ----
    let pubs = public_inputs(air, cb);
    let mut off = 0;
    let mut ood_off = vec![];
    for t in 0..nt {
        ood_off.push(off);
        let tab = &air.tables[t];
        let w = sch.w_main[t];
        let v = &proof.ood[off..off + sch.ood_len(t)];
        let (zh, sel) = selectors(ch.z, sch.heights[t]);
        let tape = Tape::compile(&tab.constraints);
        let mut regs = vec![];
        tape.eval::<EF>(&mut regs, |c, n| if n { v[w + c] } else { v[c] }, &pubs, sel);
        let mut acc = EF::ZERO;
        let mut ap = EF::ONE;
        for &o in &tape.outputs {
            acc += ap * regs[o as usize];
            ap *= ch.alpha_c;
        }
        let qoff = 2 * w + 2 * sch.w_aux[t];
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
    }

    // ---- MMCS openings ----
    let l0 = sch.l0;
    let qs = &ch.queries;
    let shape_main: Shape = (0..nt).map(|t| (sch.w_main[t], sch.log_lde(t))).collect();
    let shape_aux: Shape = (0..nt).map(|t| (8 * sch.w_aux[t], sch.log_lde(t))).collect();
    let shape_quot: Shape = (0..nt).map(|t| (8 * sch.n_quot[t], sch.log_lde(t))).collect();
    if !mmcs::verify(&shape_main, &proof.root_main, qs, &proof.open_main) {
        return Err("main opening".into());
    }
    if !mmcs::verify(&shape_aux, &proof.root_aux, qs, &proof.open_aux) {
        return Err("aux opening".into());
    }
    if !mmcs::verify(&shape_quot, &proof.root_quot, qs, &proof.open_quot) {
        return Err("quot opening".into());
    }
    let fri_q: Vec<Vec<usize>> = sch.committed.iter().map(|&(c, a)| qs.iter().map(|&j| j >> (c + a)).collect()).collect();
    for (i, &(c, a)) in sch.committed.iter().enumerate() {
        let shape: Shape = vec![(8 << a, l0 - c - a)];
        if !mmcs::verify(&shape, &proof.fri_roots[i], &fri_q[i], &proof.open_fri[i]) {
            return Err(format!("fri opening {i}"));
        }
    }
    let sets = index_sets(l0, qs);

    // batching coefficients per class layer
    let coeffs: Vec<Vec<EF>> =
        (0..sch.class_layers.len()).map(|ci| batch_coeffs(&ch.batch[ci], sch.batch_len[ci])).collect();

    // G_c at layer-c position j (= J >> c)
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
            let main = &proof.open_main.rows[t][p * w..(p + 1) * w];
            let aux = &proof.open_aux.rows[t][p * 8 * wa..(p + 1) * 8 * wa];
            let nq = sch.n_quot[t];
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

    let two_inv = F::TWO.inverse();
    for &jq in qs {
        let mut val = deep(0, jq);
        for (i, &(c, a)) in sch.committed.iter().enumerate() {
            let pos = jq >> c;
            let leaf = pos >> a;
            let fs = &fri_q[i];
            let mut sfri = fs.clone();
            sfri.sort_unstable();
            sfri.dedup();
            let p = sfri.binary_search(&leaf).unwrap();
            let w = 8 << a;
            let row = &proof.open_fri[i].rows[0][p * w..(p + 1) * w];
            let mut arr: Vec<EF> = (0..1 << a).map(|u| ef_from_coeffs(&row[8 * u..8 * u + 8])).collect();
            if arr[pos & ((1 << a) - 1)] != val {
                return Err(format!("fri layer {c} value mismatch"));
            }
            // fold a times
            let mut base = leaf << a; // layer-(c+s) position of arr[0]
            for s in 0..a {
                let layer = c + s;
                let half = arr.len() / 2;
                let mut nxt = Vec::with_capacity(half);
                for u in 0..half {
                    let x = point(l0, layer, base + 2 * u);
                    let (e0, e1) = (arr[2 * u], arr[2 * u + 1]);
                    let even = (e0 + e1) * two_inv;
                    let odd = (e0 - e1) * (F::TWO * x).inverse();
                    nxt.push(even + ch.beta[layer] * odd);
                }
                arr = nxt;
                base >>= 1;
            }
            val = arr[0];
            let nk = c + a;
            if let Some(ci) = sch.class_layers.iter().position(|&cl| cl == nk) {
                val += ch.gamma_roll[nk] * deep(ci, jq >> nk);
            }
        }
        let y = ef_from_base(point(l0, sch.fri_l, jq >> sch.fri_l));
        if val != proof.final_poly[0] + proof.final_poly[1] * y {
            return Err("final polynomial mismatch".into());
        }
    }
    Ok(())
}

/// Run all rounds of the transcript against the proof's messages.
pub fn replay(sch: &Schedule, tr: &mut Transcript, proof: &Proof) -> Challenges {
    tr.absorb(proof.root_main.to_vec());
    let alpha_fp = tr.chal();
    let gamma_mul = tr.chal();
    tr.absorb(aux_msg(&proof.root_aux, &proof.aux_finals));
    let alpha_c = tr.chal();
    tr.absorb(proof.root_quot.to_vec());
    let z = tr.chal_ood();
    tr.absorb(ood_bytes(&proof.ood));
    let batch: Vec<Vec<EF>> = sch.batch_bits.iter().map(|&b| (0..b).map(|_| tr.chal()).collect()).collect();
    let mut beta = vec![];
    let mut gamma_roll = vec![EF::ZERO; sch.fri_l + 1];
    for k in 0..sch.fri_l {
        if let Some(i) = sch.committed_at(k) {
            tr.absorb(proof.fri_roots[i].to_vec());
        }
        beta.push(tr.chal());
        if sch.class_layers.contains(&(k + 1)) {
            gamma_roll[k + 1] = tr.chal();
        }
    }
    tr.absorb(final_bytes(&proof.final_poly));
    let queries = tr.finish_queries(sch.l0, NUM_CHUNKS, PER_CHUNK);
    Challenges { alpha_fp, gamma_mul, alpha_c, z, batch, beta, gamma_roll, queries }
}
