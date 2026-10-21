//! Standalone test of the NV v2 hashing subsystem on the air2 compression AIR.
use std::sync::Arc;

use openvm_cpu_backend::CpuBackend;
use openvm_stark_backend::{
    interaction::{InteractionBuilder, PermutationCheckBus},
    prover::{AirProvingContext, ProvingContext},
    test_utils::test_system_params_small,
    AirRef, BaseAirWithPublicValues, PartitionedBaseAir, StarkEngine,
};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use super::{fmt::*, glue::{glue_matrix, GlueAir}, hash::*};
use crate::sha384::{
    compress4_air::{Layout, Sha512Air4, TableAir4, ROWS},
    compress2_trace::{sha2_compress, Comp, Rng},
    config::*,
};

fn buses() -> HashBuses {
    HashBuses { ctl: 0, k: 1, lb: 2, iface: 3, word: 4, slot: 5, job: 6, digest: 7, byte: 8 }
}

// producer row: [m_felt, m_word, m_job, m_dig, m_if, job, idx, v0, v1, v2, tag, d[18], cid, l[6]]
const PW: usize = 11 + 18 + 7 + 1 + 1; // + half flag (42-B digest tail, kind UNIT_HALF)
#[derive(Clone, Copy)]
struct Prod(HashBuses);
impl<T> BaseAir<T> for Prod {
    fn width(&self) -> usize {
        PW
    }
}
impl<T> BaseAirWithPublicValues<T> for Prod {}
impl<T> PartitionedBaseAir<T> for Prod {}
impl<AB: AirBuilder + InteractionBuilder> Air<AB> for Prod {
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        let l: Vec<AB::Expr> = main.row_slice(0).unwrap().iter().map(|&v| v.into()).collect();
        for k in 0..5 {
            b.assert_bool(l[k].clone());
        }
        self.0.send_felt(b, l[5].clone(), l[6].clone(), l[7].clone(), l[0].clone());
        b.assert_bool(l[37].clone());
        let kind = AB::Expr::from_u32(UNIT_WORD) + l[37].clone() * AB::Expr::from_u32(UNIT_HALF - UNIT_WORD);
        PermutationCheckBus::new(self.0.slot).send(
            b,
            [AB::Expr::ONE, l[5].clone(), l[6].clone(), kind, l[7].clone(), l[8].clone(), l[9].clone()],
            l[1].clone(),
        );
        self.0.send_job_tr(b, l[5].clone(), l[10].clone(), l[1].clone() * AB::Expr::ZERO + l[36].clone(), l[2].clone());
        self.0.receive_digest(b, l[5].clone(), &l[11..29], l[3].clone());
        let mut msg = vec![l[29].clone(), l[6].clone()];
        msg.extend(l[30..36].iter().cloned());
        PermutationCheckBus::new(self.0.iface).receive(b, msg, l[4].clone());
    }
}

fn jobs(rng: &mut Rng) -> Vec<Job2> {
    let mut out = vec![];
    for (i, n) in [0usize, 1, 2, 5, 13, 14, 15, 16, 17, 20, 21, 22, 23, 40, 47, 48, 49, 80, 81, 200].into_iter().enumerate() {
        let mut units = vec![];
        let mut cnt = 0;
        while cnt < n {
            if rng.next() % 3 == 0 && cnt + 2 <= n && cnt % 2 == 0 {
                units.push(U2::Word(rng.next()));
                cnt += 2;
            } else {
                let x = match rng.next() % 4 { 0 => 2013265920u32, 1 => 0x78000000 - 1, _ => (rng.next() % 2013265921) as u32 };
                units.push(U2::Felt(x));
                cnt += 1;
            }
        }
        out.push(Job2 { id: i as u32, node: false, tag: [0u8, 3, 4, 5, 6][i % 5], units, wread: 0 });
    }
    // Merkle-node jobs: 12 aligned word units
    for t in 0..3 {
        let mut units = digest_units(std::array::from_fn(|_| rng.next()));
        units.extend(digest_units(std::array::from_fn(|_| rng.next())));
        out.insert(2 * t + 1, Job2 { id: 100 + t as u32, node: true, tag: 0, units, wread: 0 });
    }
    // commit-shaped transcript jobs (48 B: 6 word units; 42 B: 5 words + 2-byte tail)
    for t in 0..2 {
        let mut units = vec![U2::Felt(48), U2::Felt(0)];
        units.extend((0..6).map(|_| U2::Word(rng.next())));
        units.push(U2::Felt(crate::sha384::config::sha_levers().digest_bytes as u32));
        units.push(U2::Felt(0));
        units.extend(digest_units(std::array::from_fn(|_| rng.next())));
        out.push(Job2 { id: 200 + t as u32, node: false, tag: 4, units, wread: 0 });
    }
    out
}

fn prod_trace(work: &Work2, dig: &[[u64; 6]]) -> RowMajorMatrix<F> {
    let mut rows: Vec<[u32; PW]> = vec![];
    for (job, j) in work.jobs.iter().enumerate() {
        let mut r = [0u32; PW];
        r[2] = 1;
        r[5] = j.id;
        r[10] = if j.node { NODE_TAG } else { j.tag as u32 };
        r[36] = (j.node || j.tag == 0 || j.tag == crate::sha384::config::TAG_COSET_LEAF) as u32;
        rows.push(r);
        let mut idx = 0;
        for u in &j.units {
            let mut r = [0u32; PW];
            r[5] = j.id;
            r[6] = idx;
            match *u {
                U2::Felt(x) => {
                    r[0] = 1;
                    r[7] = x;
                }
                U2::Word(w) => {
                    r[1] = 1;
                    let l = wl(w);
                    r[7..10].copy_from_slice(&l);
                }
                U2::Half(w) => {
                    r[1] = 1;
                    // prefix-job tails are UNIT_HALF; node-job tails ride the fixed node framing (kind word)
                    r[37] = (!j.node) as u32;
                    let l = wl(w & 0xffff_0000_0000_0000);
                    r[7..10].copy_from_slice(&l);
                }
            }
            idx += u.nunits() as u32;
            rows.push(r);
        }
        let mut r = [0u32; PW];
        r[3] = 1;
        r[5] = j.id;
        let trunc = crate::sha384::config::sha_levers().digest_bytes == 42
            && (j.node || j.tag == 0 || j.tag == crate::sha384::config::TAG_COSET_LEAF);
        for q in 0..6 {
            let w = if trunc && q == 5 { dig[job][q] & 0xffff_0000_0000_0000 } else { dig[job][q] };
            let l = wl(w);
            r[11 + 3 * q..14 + 3 * q].copy_from_slice(&l);
        }
        rows.push(r);
    }
    for (s, c) in work.nodes.iter().enumerate() {
        let out = sha2_compress(c);
        let ws: Vec<u64> = c.h.iter().chain(c.block.iter()).chain(out.iter()).copied().collect();
        for m in 0..16 {
            let mut r = [0u32; PW];
            r[4] = 1;
            r[6] = m as u32;
            r[29] = (s * ROWS) as u32;
            r[30..33].copy_from_slice(&wl(ws[2 * m]));
            r[33..36].copy_from_slice(&wl(ws[2 * m + 1]));
            rows.push(r);
        }
    }
    let h = rows.len().next_power_of_two();
    rows.resize(h, [0; PW]);
    RowMajorMatrix::new(rows.into_iter().flatten().map(F::from_u32).collect(), PW)
}

fn run(work: &Work2, mutate: Option<(usize, usize, usize)>) {
    let b = buses();
    let lay = Layout::new(sha_k());
    let t = generate2(work, lay, None);
    for (j, d) in work.jobs.iter().zip(&t.job_digests) {
        use sha2::Digest as _;
        let native: [u8; 48] = sha2::Sha384::digest(j.message()).into();
        assert_eq!(digest_bytes(digest_from_words(*d)), native);
    }
    let airs: Vec<AirRef<Sha384Config>> = vec![
        Arc::new(Sha512Air4 { lay, buses: b.sha(), cid_offset: 0 }),
        Arc::new(TableAir4 { lay, buses: b.sha() }),
        Arc::new(GlueAir { buses: b }),
        Arc::new(ByteAir { buses: b }),
        Arc::new(Prod(b)),
    ];
    let mut mats = vec![t.compress, t.table, glue_matrix(&t.glue_rows, 1), byte_table2(&t.byte_counts), prod_trace(work, &t.job_digests)];
    if let Some((m, r, c)) = mutate {
        let w = mats[m].width();
        mats[m].values[r * w + c] += F::ONE;
    }
    let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = mats.into_iter().map(AirProvingContext::simple_no_pis).collect();
    let mut params = test_system_params_small(2, 18, 3);
    params.max_constraint_degree = lay.degree().max(4);
    let engine = Sha384CpuEngine::new(params);
    engine.debug(&airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
}

#[test]
fn nv_hash2_random_jobs() {
    let mut rng = Rng(0x5eed_1234_abcd_0001);
    let jobs = jobs(&mut rng);
    let nodes: Vec<Comp> = (0..3).map(|_| rng.comp()).collect();
    run(&Work2 { jobs, nodes }, None);
}

#[test]
fn nv_hash2_rejects_mutations() {
    let mut rng = Rng(0x0dd5_eed0_0000_0002);
    let jobs = jobs(&mut rng)[..10].to_vec();
    let work = Work2 { jobs, nodes: vec![] };
    run(&work, None);
    // GLUE bytes / flags / splits / state pairs (column 0 = role flag)
    let gc = |name: &str| -> usize {
        match name {
            "cid" => 6, "act" => 10, "uidx" => 12, "b1" => 14, "b5" => 18, "b7" => 20, "b9" => 22,
            "carry" => 29, "lo0" => 30, "ulo0" => 34, "p0" => 38, "wd0" => 42, "s0" => 48,
            _ => unreachable!(),
        }
    };
    let mut cases = vec![];
    for r in [2usize, 3, 5, 9, 12, 14] {
        for n in ["cid", "act", "uidx", "b1", "b5", "b7", "b9", "carry", "lo0", "ulo0", "p0", "wd0", "s0"] {
            cases.push((2usize, r, gc(n)));
        }
    }
    cases.push((4, 3, 7));
    for case in cases {
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&work, Some(case))));
        assert!(res.is_err(), "mutation {case:?} accepted");
    }
}
