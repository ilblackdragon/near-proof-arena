//! NV-faithful §2(c): tamper tests for the SHA-384 compression AIR v2.1 and the GLUE role
//! (results/pq-recursion-nv/FAITHFUL.md).  Every attack trace is built *outside* the
//! `catch_unwind`, so a rejection can only come from the debug constraint / LogUp checker.
//!
//! 42-byte-digest cases run only when the process has NEARPROOF_DIGEST_BYTES=42 (the hash
//! levers are process-global); they print `NV_FAITHFUL_SKIP` otherwise.
use std::{
    panic::{catch_unwind, AssertUnwindSafe},
    sync::Arc,
};

use openvm_cpu_backend::CpuBackend;
use openvm_stark_backend::{
    interaction::{InteractionBuilder, PermutationCheckBus},
    prover::{AirProvingContext, ProvingContext},
    test_utils::test_system_params_small,
    AirRef, BaseAirWithPublicValues, PartitionedBaseAir, StarkEngine,
};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use super::{
    fmt::*,
    glue::{glue_matrix, GlueAir, GlueCols, GLUE_W},
    hash::*,
};
use crate::sha384::{
    compress2_air::{all_sign_coefs, big_sigma0, big_sigma1, ch2, limbs_of_signs, maj2, small_sigma0, small_sigma1, word},
    compress2_trace::{bsig0, bsig1, chf, majf, ssig0, ssig1, Comp, Rng},
    compress4_air::{Layout, Sha512Air4, TableAir4, ROWS},
    compress4_trace::{gen_main, gen_table, main_height},
    config::*,
};

fn buses() -> HashBuses {
    HashBuses { ctl: 0, k: 1, lb: 2, iface: 3, word: 4, slot: 5, job: 6, digest: 7, byte: 8 }
}

// producer row: [m_felt, m_word, m_job, m_dig, m_if, job, idx, v0, v1, v2, tag, d[18], cid, l[6], tr, half]
const PW: usize = 38;
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
        b.assert_bool(l[37].clone());
        self.0.send_felt(b, l[5].clone(), l[6].clone(), l[7].clone(), l[0].clone());
        // word units (kind UNIT_WORD) and 42-B digest tails (kind UNIT_HALF), as the ALU sends them
        let kind = AB::Expr::from_u32(UNIT_WORD) + l[37].clone() * AB::Expr::from_u32(UNIT_HALF.wrapping_sub(UNIT_WORD));
        PermutationCheckBus::new(self.0.slot).send(
            b,
            [AB::Expr::ONE, l[5].clone(), l[6].clone(), kind, l[7].clone(), l[8].clone(), l[9].clone()],
            l[1].clone(),
        );
        self.0.send_job_tr(b, l[5].clone(), l[10].clone(), l[36].clone(), l[2].clone());
        self.0.receive_digest(b, l[5].clone(), &l[11..29], l[3].clone());
        let mut msg = vec![l[29].clone(), l[6].clone()];
        msg.extend(l[30..36].iter().cloned());
        PermutationCheckBus::new(self.0.iface).receive(b, msg, l[4].clone());
    }
}

fn is_merkle(j: &Job2) -> bool {
    j.node || j.tag == 0 || j.tag == TAG_COSET_LEAF
}

/// Producer rows for the units of `units_of` (job order = `dig` order).
fn prod_trace(units_of: &Work2, dig: &[[u64; 6]]) -> RowMajorMatrix<F> {
    let mut rows: Vec<[u32; PW]> = vec![];
    for (job, j) in units_of.jobs.iter().enumerate() {
        let mut r = [0u32; PW];
        r[2] = 1;
        r[5] = j.id;
        r[10] = if j.node { NODE_TAG } else { j.tag as u32 };
        r[36] = is_merkle(j) as u32;
        rows.push(r);
        let mut idx = 0;
        for u in &j.units {
            let mut r = [0u32; PW];
            r[5] = j.id;
            r[6] = idx;
            match *u {
                U2::Felt(x) => {
                    r[0] = 1;
                    r[7] = F::from_u32(x).as_canonical_u32();
                }
                U2::Word(w) => {
                    r[1] = 1;
                    r[7..10].copy_from_slice(&wl(w));
                }
                U2::Half(w) => {
                    r[1] = 1;
                    // prefix-job tails are UNIT_HALF; node-job tails ride the fixed node framing (kind word)
                    r[37] = (!j.node) as u32;
                    r[7..10].copy_from_slice(&wl(w & 0xffff_0000_0000_0000));
                }
            }
            idx += u.nunits() as u32;
            rows.push(r);
        }
        let mut r = [0u32; PW];
        r[3] = 1;
        r[5] = j.id;
        let trunc = sha_levers().digest_bytes == 42 && is_merkle(j);
        for q in 0..6 {
            let w = if trunc && q == 5 { dig[job][q] & 0xffff_0000_0000_0000 } else { dig[job][q] };
            r[11 + 3 * q..14 + 3 * q].copy_from_slice(&wl(w));
        }
        rows.push(r);
    }
    let h = rows.len().next_power_of_two();
    rows.resize(h, [0; PW]);
    RowMajorMatrix::new(rows.into_iter().flatten().map(F::from_u32).collect(), PW)
}

struct Inst {
    airs: Vec<AirRef<Sha384Config>>,
    /// [compress, table, glue, byte, producer]
    mats: Vec<RowMajorMatrix<F>>,
    lay: Layout,
    /// compressions in SHA-trace order
    comps: Vec<Comp>,
    counts: Vec<u32>,
}

/// GLUE + SHA traces for `glue_work`, producer for `units_of` (same job ids / order).
fn inst(glue_work: &Work2, units_of: &Work2) -> Inst {
    let b = buses();
    let lay = Layout::new(sha_k());
    let t = generate2(glue_work, lay, None);
    let comps: Vec<Comp> = glue_work.jobs.iter().flat_map(|j| sha384_blocks(&j.message()).0).collect();
    let airs: Vec<AirRef<Sha384Config>> = vec![
        Arc::new(Sha512Air4 { lay, buses: b.sha(), cid_offset: 0 }),
        Arc::new(TableAir4 { lay, buses: b.sha() }),
        Arc::new(GlueAir { buses: b }),
        Arc::new(ByteAir { buses: b }),
        Arc::new(Prod(b)),
    ];
    let mats = vec![
        t.compress,
        t.table,
        glue_matrix(&t.glue_rows, 1),
        byte_table2(&t.byte_counts),
        prod_trace(units_of, &t.job_digests),
    ];
    Inst { airs, mats, lay, comps, counts: t.byte_counts }
}

/// Debug-check; true = accepted.
fn accepted(i: &Inst) -> bool {
    let mats = i.mats.clone();
    let lay = i.lay;
    let airs = i.airs.clone();
    catch_unwind(AssertUnwindSafe(move || {
        let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> =
            mats.into_iter().map(AirProvingContext::simple_no_pis).collect();
        let mut params = test_system_params_small(2, 18, 3);
        params.max_constraint_degree = lay.degree().max(4);
        let engine = Sha384CpuEngine::new(params);
        engine.debug(&airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
    }))
    .is_ok()
}

fn expect(name: &str, i: &Inst, ok: bool) {
    let a = accepted(i);
    assert_eq!(a, ok, "case `{name}`: accepted = {a}, expected {ok}");
    println!("NV_FAITHFUL {} {name}", if ok { "ACCEPTED" } else { "REJECTED" });
}

fn glue_row(m: &mut RowMajorMatrix<F>, r: usize) -> &mut GlueCols<F> {
    use core::borrow::BorrowMut;
    let w = m.width();
    m.values[r * w + 1..r * w + 1 + GLUE_W].borrow_mut()
}
fn glue_get(m: &RowMajorMatrix<F>, r: usize) -> &GlueCols<F> {
    use core::borrow::Borrow;
    let w = m.width();
    m.values[r * w + 1..r * w + 1 + GLUE_W].borrow()
}
fn nglue(m: &RowMajorMatrix<F>) -> usize {
    (0..m.height()).filter(|&r| m.values[r * m.width()] == F::ONE).count()
}
fn rebuild_bytes(i: &mut Inst) {
    i.mats[3] = byte_table2(&i.counts);
}
fn u(x: F) -> usize {
    x.as_canonical_u32() as usize
}

fn base_jobs(rng: &mut Rng) -> Vec<Job2> {
    let mut out = vec![];
    for (i, n) in [3usize, 14, 22, 49].into_iter().enumerate() {
        let mut units = vec![];
        let mut cnt = 0;
        while cnt < n {
            if cnt % 2 == 0 && cnt + 2 <= n && rng.next() % 2 == 0 {
                units.push(U2::Word(rng.next()));
                cnt += 2;
            } else {
                units.push(U2::Felt((rng.next() % 2013265921) as u32));
                cnt += 1;
            }
        }
        out.push(Job2 { id: i as u32, node: false, tag: [0u8, 3, 5, 6][i], units, wread: 0 });
    }
    out
}

/// 42-B commit job: the digest tail (top 2 bytes of word 5) must be framed as a 2-byte tail.
/// Attack: frame the same unit (same limbs (0, 0, top16 << 6)) as a full 8-byte word.  Both
/// framings are internally consistent; before the UNIT_HALF fix the circuit accepted both, so
/// the transcript state after every 42-B commit was a prover choice (1 bit per commit).
#[test]
fn nv_faithful_tail_framing_unique() {
    if sha_levers().digest_bytes != 42 {
        println!("NV_FAITHFUL_SKIP tail framing (needs NEARPROOF_DIGEST_BYTES=42)");
        return;
    }
    let mut rng = Rng(0x7a11_f4a3_0000_0001);
    let state: [u64; 6] = std::array::from_fn(|_| rng.next());
    let mut d: [u64; 6] = std::array::from_fn(|_| rng.next());
    d[5] &= 0xffff_0000_0000_0000; // a native 42-B digest (bytes 42..48 zero)
    let mut units = vec![U2::Felt(48), U2::Felt(0)];
    units.extend(state.iter().map(|&w| U2::Word(w)));
    units.push(U2::Felt(42));
    units.push(U2::Felt(0));
    units.extend(digest_units(d));
    assert!(matches!(units.last(), Some(U2::Half(_))));
    let honest = Job2 { id: 7, node: false, tag: TAG_COMMIT, units: units.clone(), wread: 0 };
    // native framing: hash_parts(TAG_COMMIT, [state, digest_wire(d)])
    let sb: Vec<u8> = state.iter().flat_map(|w| w.to_be_bytes()).collect();
    let dw = digest_wire(digest_from_words(d));
    assert_eq!(honest.message(), hash_parts_message(TAG_COMMIT, &[&sb, &dw]));
    let w_honest = Work2 { jobs: vec![honest], nodes: vec![] };
    expect("commit tail framed as tail", &inst(&w_honest, &w_honest), true);
    let mut alt_units = units;
    *alt_units.last_mut().unwrap() = U2::Word(d[5]);
    let alt = Job2 { id: 7, node: false, tag: TAG_COMMIT, units: alt_units, wread: 0 };
    assert_ne!(alt.message(), w_honest.jobs[0].message());
    let w_alt = Work2 { jobs: vec![alt], nodes: vec![] };
    expect("commit tail re-framed as a full word", &inst(&w_alt, &w_honest), false);
}

/// The fractional-split attack on `limbs_from_bytes`: lo5 -> lo5 - 1/8 with b6 += 32 keeps
/// limb 0 (65536 * (1/8) = 8192 = 32 * 256) and both byte-table lookups valid, but limb 1
/// moves by 1/256, so the interface bus rejects (FAITHFUL.md §2(c), "×256 argument").
#[test]
fn nv_faithful_limb_split_fractional() {
    let mut rng = Rng(0x11b5_0000_0000_0002);
    let w = Work2 { jobs: base_jobs(&mut rng), nodes: vec![] };
    let mut i = inst(&w, &w);
    expect("honest", &i, true);
    let (a5, a2) = split_bits();
    let inv8 = F::from_u32(1 << (8 - a5)).inverse();
    let g = &i.mats[2];
    let r = (0..nglue(g))
        .find(|&r| {
            let c = glue_get(g, r);
            u(c.lo[0]) >= 1 && u(c.b[6]) < 256 - (1 << (8 - a5 + 2)) && u(c.act) == 1
        })
        .expect("row");
    let c = glue_get(&i.mats[2], r);
    let (b6, b7, lo0, lo1) = (u(c.b[6]), u(c.b[7]), u(c.lo[0]), u(c.lo[1]));
    let before = limbs_from_bytes(&core::array::from_fn(|k| c.b[k]), c.lo[0], c.lo[1]);
    let bump = 1usize << (16 - 8 - (8 - a5)); // 2^(8 + a5 - 8) bytes of b6 per unit of lo5/2^(8-a5)
    {
        let c = glue_row(&mut i.mats[2], r);
        c.lo[0] -= inv8;
        c.b[6] += F::from_usize(bump);
    }
    let c = glue_get(&i.mats[2], r);
    let after = limbs_from_bytes(&core::array::from_fn(|k| c.b[k]), c.lo[0], c.lo[1]);
    assert_eq!(before[0], after[0], "limb 0 must be unchanged by the fractional split");
    assert_ne!(before[1], after[1]);
    // keep every byte lookup valid: (b6, b7) and (lo0 * 2^(8-a5), lo1 * 2^(8-a2))
    i.counts[b6 + 256 * b7] -= 1;
    i.counts[b6 + bump + 256 * b7] += 1;
    let (x, y) = (lo0 << (8 - a5), lo1 << (8 - a2));
    i.counts[x + 256 * y] -= 1;
    i.counts[x - 1 + 256 * y] += 1;
    let _ = a2;
    rebuild_bytes(&mut i);
    expect("fractional lo5 split with b6 compensation", &i, false);
}

/// Exhaustive form of the ×256 argument: for canonical limbs of a word, the only
/// (bytes, lo5, lo2) with lo5 * 2^(8-a5), lo2 * 2^(8-a2) bytes and limbs_from_bytes = limbs is
/// the big-endian encoding.  For each of the 2^16 (V5, U2) pairs the bytes are forced.
#[test]
fn nv_faithful_limb_split_exhaustive() {
    let (a5, a2) = split_bits();
    let o = limb_off();
    assert_eq!(sha_k(), 3, "argument written for k = 3");
    let mut rng = Rng(0x5eed_0000_0000_0003);
    let mut words: Vec<u64> = vec![0, u64::MAX, 1 << 63, 0x00ff_00ff_00ff_00ff, 0xff00_ff00_ff00_ff00];
    words.extend((0..40).map(|_| rng.next()));
    let p = 2013265921u64;
    let inv = |x: u64| -> u64 { F::from_u64(x).inverse().as_canonical_u32() as u64 };
    for &wd in &words {
        let l = wl(wd).map(|x| x as u64);
        let mut sols = 0;
        for v5 in 0..256u64 {
            for u2 in 0..256u64 {
                // lo5 = v5 / 2^(8-a5), lo2 = u2 / 2^(8-a2) (field)
                let lo5 = v5 * inv(1 << (8 - a5)) % p;
                let lo2 = u2 * inv(1 << (8 - a2)) % p;
                // limb 0: b7 + 2^8 b6 = l0 - 2^16 lo5
                let r0 = (l[0] + p - (65536 * lo5) % p) % p;
                if r0 >= 65536 {
                    continue;
                }
                // limb 1: hi5 + 2^3 b4 + 2^11 b3 = l1 - 2^19 lo2, hi5 = (b5 - lo5) / 2^a5: search b5
                let r1 = (l[1] + p - ((1u64 << (40 - o[1])) * lo2) % p) % p;
                let mut ok1 = false;
                for b5 in 0..256u64 {
                    let hi5 = (b5 + p - lo5) % p * inv(1 << a5) % p;
                    let rest = (r1 + p - hi5) % p; // = 8 b4 + 2048 b3
                    if rest < (1 << 19) && rest % 8 == 0 {
                        ok1 = true;
                    }
                }
                if !ok1 {
                    continue;
                }
                let mut ok2 = false;
                for b2 in 0..256u64 {
                    let hi2 = (b2 + p - lo2) % p * inv(1 << a2) % p;
                    let rest = (l[2] + p - hi2) % p; // = 64 b1 + 16384 b0
                    if rest < (1 << 22) && rest % 64 == 0 {
                        ok2 = true;
                    }
                }
                if ok2 {
                    sols += 1;
                    assert!(v5 % (1 << (8 - a5)) == 0 && u2 % (1 << (8 - a2)) == 0, "fractional split solution for {wd:#x}: v5 {v5} u2 {u2}");
                }
            }
        }
        assert_eq!(sols, 1, "word {wd:#x}: {sols} split solutions");
    }
}

/// Felt units are canonical: bytes of x + p (top byte 0x78, low bytes not all zero) are
/// rejected; p - 1 (the zm case) is accepted.
#[test]
fn nv_faithful_noncanonical_felt() {
    let p = 2013265921u32;
    let job = |x: u32| Job2 { id: 0, node: false, tag: 3, units: vec![U2::Felt(5), U2::Felt(x), U2::Felt(9)], wread: 0 };
    let ok = Work2 { jobs: vec![job(p - 1)], nodes: vec![] };
    expect("felt p-1", &inst(&ok, &ok), true);
    for x in [p, p + 5, 0x78ff_ffff] {
        let w = Work2 { jobs: vec![job(x)], nodes: vec![] };
        // the producer sends x mod p (what the ALU's value is); the bytes encode x >= p
        expect(&format!("felt bytes of {x:#x} (= {} mod p)", x % p), &inst(&w, &w), false);
    }
}

/// Zero-padding rows cannot hold a compression: a fully consistent extra segment after the
/// last one (no GLUE consumer) and a reordering of two segments are rejected.
#[test]
fn nv_faithful_fake_and_reordered_segments() {
    let mut rng = Rng(0xfa4e_0000_0000_0004);
    let w = Work2 { jobs: base_jobs(&mut rng), nodes: vec![] };
    let base = inst(&w, &w);
    expect("honest", &base, true);
    let lay = base.lay;
    let regen = |i: &mut Inst, comps: &[Comp]| {
        let h = main_height(comps.len()).max(i.mats[0].height());
        let m = gen_main(comps, h);
        let t = gen_table(&m, h);
        i.mats[0] = RowMajorMatrix::new(m.into_iter().map(F::from_u32).collect(), lay.width);
        i.mats[1] = RowMajorMatrix::new(t.into_iter().map(F::from_u32).collect(), crate::sha384::compress4_air::T_WIDTH);
    };
    // extra consistent segment in the zero tail
    let mut i = inst(&w, &w);
    let mut comps = i.comps.clone();
    assert!((comps.len() + 1) * ROWS <= i.mats[0].height(), "need tail room");
    comps.push(rng.comp());
    regen(&mut i, &comps);
    expect("extra consistent segment in the zero tail", &i, false);
    // the same extra segment as a copy of a consumed compression
    let mut i = inst(&w, &w);
    let mut comps = i.comps.clone();
    comps.push(comps[1]);
    regen(&mut i, &comps);
    expect("duplicate of a consumed compression in the tail", &i, false);
    // two segments swapped
    let mut i = inst(&w, &w);
    let mut comps = i.comps.clone();
    comps.swap(0, 1);
    regen(&mut i, &comps);
    expect("two segments swapped", &i, false);
}

/// The bit-sign polynomials and sign-limb recomposition are exact on every digit value, and
/// the sign forms of Σ0, Σ1, σ0, σ1, Ch, Maj equal FIPS 180-4 (k = 1, 2, 3).
#[test]
fn nv_faithful_sign_polys() {
    let mut rng = Rng(0x5195_0000_0000_0005);
    for k in 1..=3usize {
        let lay = crate::sha384::compress2_air::Layout::new(k);
        let coef = all_sign_coefs::<F>(k);
        let mut xs: Vec<u64> = (0..(1u64 << k)).map(|v| (0..lay.nd).fold(0u64, |a, j| a | ((v & ((1 << lay.dsize(j)) - 1)) << (k * j)))).collect();
        xs.extend((0..64).map(|_| rng.next()));
        let wv = |x: u64| {
            let row: Vec<F> = lay.digits(x).into_iter().map(F::from_u64).collect();
            word::<F, F>(&lay, &coef, &row, 0)
        };
        let half = F::from_u32(2).inverse();
        let lim = |x: u64| lay.limbs(x).map(F::from_u64);
        for (t, &x) in xs.iter().enumerate() {
            let w = wv(x);
            for i in 0..64 {
                let s = if (x >> i) & 1 == 1 { -F::ONE } else { F::ONE };
                assert_eq!(w.sg[i], s, "k {k} x {x:#x} bit {i}");
            }
            assert_eq!(w.limbs, lim(x));
            let (y, z) = (xs[(t + 1) % xs.len()], xs[(t + 2) % xs.len()]);
            let (wy, wz) = (wv(y), wv(z));
            assert_eq!(limbs_of_signs::<F, F>(&lay, &big_sigma0(&w.sg), F::ONE), lim(bsig0(x)));
            assert_eq!(limbs_of_signs::<F, F>(&lay, &big_sigma1(&w.sg), F::ONE), lim(bsig1(x)));
            assert_eq!(limbs_of_signs::<F, F>(&lay, &small_sigma0(&w.sg), F::ONE), lim(ssig0(x)));
            assert_eq!(limbs_of_signs::<F, F>(&lay, &small_sigma1(&w.sg), F::ONE), lim(ssig1(x)));
            assert_eq!(limbs_of_signs::<F, F>(&lay, &ch2(&w.sg, &wy.sg, &wz.sg), half), lim(chf(x, y, z)));
            assert_eq!(limbs_of_signs::<F, F>(&lay, &maj2(&w.sg, &wy.sg, &wz.sg), half), lim(majf(x, y, z)));
        }
    }
    println!("NV_FAITHFUL sign polynomials exact for k = 1, 2, 3");
}

/// 42-B Merkle digests: lo6 (the truncated low 6 bits of limb 2 of word 5) is not free.
#[test]
fn nv_faithful_lo6_pinned() {
    if sha_levers().digest_bytes != 42 {
        println!("NV_FAITHFUL_SKIP lo6 (needs NEARPROOF_DIGEST_BYTES=42)");
        return;
    }
    let mut rng = Rng(0x1060_0000_0000_0006);
    let w = Work2 { jobs: base_jobs(&mut rng), nodes: vec![] };
    let i0 = inst(&w, &w);
    expect("honest", &i0, true);
    let g = &i0.mats[2];
    // last-block q = 6 row of the first Merkle job (tag 0 => tr = 1)
    let r = (0..nglue(g))
        .find(|&r| {
            let c = glue_get(g, r);
            c.tr == F::ONE && c.last == F::ONE && c.q.map(u) == [0, 1, 1]
        })
        .expect("merkle q6 row");
    let lo6 = u(glue_get(g, r).lo6);
    for (name, delta) in [("lo6 + 1", F::ONE), ("lo6 + 1/4 (fractional)", F::from_u32(4).inverse())] {
        let mut i = inst(&w, &w);
        glue_row(&mut i.mats[2], r).lo6 += delta;
        let nl = u(glue_get(&i.mats[2], r).lo6) * 4 % 2013265921;
        let newv = (F::from_usize(lo6) + delta) * F::from_u32(4);
        let _ = nl;
        // keep the byte lookup of lo6 valid where possible (old pattern: lo6 * 4 byte)
        let nv = u(newv);
        if nv < 256 {
            i.counts[lo6 * 4] -= 1;
            i.counts[nv] += 1;
            rebuild_bytes(&mut i);
        }
        expect(name, &i, false);
    }
}
