//! pq-nv-preprocessed: NV verifying children with preprocessed (vk-committed) and cached traces
//! (results/pq-nv-preprocessed/DESIGN.md §5).
use openvm_stark_backend::{
    keygen::types::MultiStarkVerifyingKey,
    proof::Proof,
    test_utils::{CachedFixture11, FibFixture, PreprocessedAndCachedFixture, PreprocessedFibFixture, TestFixture},
    StarkEngine,
};
use p3_field::PrimeCharacteristicRing;

use super::{builder::Builder, verifier::build_verifier};
use crate::sha384::{config::*, e2e_tests::child_params_small};

type Vk = MultiStarkVerifyingKey<Sha384Config>;
type Pf = Proof<Sha384Config>;

/// Child selector table (the preprocessed column of FibonacciSelectorAir), 32 rows.
fn sels(seed: usize) -> Vec<bool> {
    (0..32).map(|i| (i * 7 + seed) % 3 != 0).collect()
}

fn engine() -> Sha384CpuEngine {
    Sha384CpuEngine::new(child_params_small())
}

/// Program for (vk, proof) (generation only: failures are recorded, the program is returned).
fn program(vk: &Vk, proof: &Pf) -> Builder {
    let mut b = Builder::new(17, 0);
    build_verifier(&mut b, vk, proof);
    b
}

/// Honest child: native verify passes, the program records no failure and ends in the native
/// transcript state.
fn honest(vk: &Vk, proof: &Pf) -> Builder {
    let e = engine();
    e.verify(vk, proof).expect("native verify");
    let b = program(vk, proof);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    let mut t = ShaTranscript::default();
    openvm_stark_backend::verifier::verify(e.config(), vk, proof, &mut t).unwrap();
    assert_eq!(t.state, b.transcript.inner.state, "transcript diverged from native");
    b
}

/// Full NV constraint check (all AIRs, all buses) of the trace generated for (vk, proof).
fn debug(vk: &Vk, proof: &Pf, log_rows: usize) {
    use openvm_cpu_backend::CpuBackend;
    use openvm_stark_backend::prover::{AirProvingContext, ProvingContext};
    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), log_rows, 1);
    let airs = circ.airs::<Sha384Config>();
    let (mats, b) = circ.generate(vk, proof);
    let pv = b.public_values();
    let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = mats
        .into_iter()
        .enumerate()
        .map(|(i, m)| if i == 0 { AirProvingContext::simple(m, pv.clone()) } else { AirProvingContext::simple_no_pis(m) })
        .collect();
    let mut p = crate::sha384::e2e_tests::parent_params_debug();
    p.max_constraint_degree = circ.layout().degree().max(6);
    Sha384CpuEngine::new(p).debug(&airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
}

fn must_fail(name: &str, f: impl FnOnce()) {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    assert!(r.is_err(), "`{name}` accepted");
    println!("NV_PREP_REJECTED {name}");
}

fn n_commits(proof: &Pf) -> usize {
    proof.whir_proof.initial_round_opened_rows.len()
}

/// Honest preprocessed child: the program verifies it, matches the native transcript, does not
/// depend on the witness (two different Fibonacci seeds over the same table), and the generated
/// NV trace satisfies every NV constraint.
#[test]
fn nv_prep_honest() {
    let e = engine();
    let (vk, proof) = PreprocessedFibFixture::new(0, 1, sels(0)).keygen_and_prove(&e);
    assert_eq!(n_commits(&proof), 2, "main + preprocessed");
    let b = honest(&vk, &proof);
    let (vk2, proof2) = PreprocessedFibFixture::new(2, 3, sels(0)).keygen_and_prove(&e);
    assert_eq!(vk.pre_hash, vk2.pre_hash);
    let b2 = honest(&vk2, &proof2);
    assert_eq!(b.instrs, b2.instrs, "program depends on proof values");
    // the same AIR without a preprocessed trace for scale: the plain Fib child
    let (vkf, prf) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&e);
    let bf = honest(&vkf, &prf);
    println!(
        "NV_PREP_ROWS prep={} jobs={} merkle_nodes={} | fib={} jobs={} merkle_nodes={}",
        b.instrs.len(),
        b.job_units.len(),
        b.merkle_nodes,
        bf.instrs.len(),
        bf.job_units.len(),
        bf.merkle_nodes
    );
    debug(&vk, &proof, 16);
}

/// The preprocessed commitment in the child vk is tampered with (pre-hash kept): the program's
/// constant root differs from the tree the child opened. Rejected by the program (Merkle root,
/// and the transcript, which observes the constant) and by the NV constraints.
#[test]
fn nv_prep_tampered_commitment() {
    let e = engine();
    let (vk, proof) = PreprocessedFibFixture::new(0, 1, sels(0)).keygen_and_prove(&e);
    let mut bad = vk.clone();
    bad.inner.per_air[0].preprocessed_data.as_mut().unwrap().commit[0] ^= 1;
    assert!(e.verify(&bad, &proof).is_err(), "native accepts a tampered commitment");
    let b = program(&bad, &proof);
    println!("NV_PREP tampered commitment: {:?}", b.failures);
    assert!(b.failures.iter().any(|f| f == "merkle root"), "{:?}", b.failures);
    must_fail("tampered preprocessed commitment (circuit)", || debug(&bad, &proof, 16));
    // the proof's opened preprocessed rows tampered with (commitment honest): Merkle root
    let mut badp = proof.clone();
    badp.whir_proof.initial_round_opened_rows[1][0][0][0] += F::ONE;
    let b = program(&vk, &badp);
    assert!(b.failures.iter().any(|f| f == "merkle root"), "{:?}", b.failures);
    must_fail("tampered preprocessed opened row (circuit)", || debug(&vk, &badp, 16));
    // the preprocessed column opening tampered with: constraint / stacking checks
    let mut badc = proof.clone();
    badc.batch_constraint_proof.column_openings[0][1][0] += EF::ONE;
    let b = program(&vk, &badc);
    println!("NV_PREP tampered preprocessed opening: {:?}", b.failures);
    assert!(!b.failures.is_empty());
    must_fail("tampered preprocessed column opening (circuit)", || debug(&vk, &badc, 16));
}

/// Wrong vk constant: the program is generated from a vk whose pre-hash differs from the one the
/// child's transcript used. Rejected.
#[test]
fn nv_prep_wrong_vk_constant() {
    let e = engine();
    let (vk, proof) = PreprocessedFibFixture::new(0, 1, sels(0)).keygen_and_prove(&e);
    let mut bad = vk.clone();
    bad.pre_hash[0] ^= 1;
    assert!(e.verify(&bad, &proof).is_err());
    let b = program(&bad, &proof);
    println!("NV_PREP wrong pre-hash: {} failures, first {:?}", b.failures.len(), b.failures.first());
    assert!(!b.failures.is_empty());
    must_fail("wrong vk pre-hash (circuit)", || debug(&bad, &proof, 16));
}

/// A child proved against a different preprocessed table (same AIR, same heights, different
/// selector column, hence a different commitment and vk), checked by the program for the
/// original table. Rejected; both directions.
#[test]
fn nv_prep_other_table() {
    let e = engine();
    let (vk_a, proof_a) = PreprocessedFibFixture::new(0, 1, sels(0)).keygen_and_prove(&e);
    let (vk_b, proof_b) = PreprocessedFibFixture::new(0, 1, sels(1)).keygen_and_prove(&e);
    let ca = vk_a.inner.per_air[0].preprocessed_data.as_ref().unwrap().commit;
    let cb = vk_b.inner.per_air[0].preprocessed_data.as_ref().unwrap().commit;
    assert_ne!(ca, cb, "tables must differ");
    honest(&vk_b, &proof_b);
    for (name, vk, proof) in [("table B under A's program", &vk_a, &proof_b), ("table A under B's program", &vk_b, &proof_a)] {
        assert!(e.verify(vk, proof).is_err());
        let b = program(vk, proof);
        println!("NV_PREP {name}: {} failures, first {:?}", b.failures.len(), b.failures.first());
        assert!(!b.failures.is_empty());
        must_fail(name, || debug(vk, proof, 16));
    }
    // a vk that claims table B's commitment but keeps A's pre-hash, on A's proof: the program's
    // constant root (B) is not the tree A's proof opens
    let mut mixed = vk_a.clone();
    mixed.inner.per_air[0].preprocessed_data.as_mut().unwrap().commit = cb;
    let b = program(&mixed, &proof_a);
    assert!(b.failures.iter().any(|f| f == "merkle root"), "{:?}", b.failures);
    must_fail("A's proof under a vk claiming table B", || debug(&mixed, &proof_a, 16));
}

/// Cached traces (the commitment is a proof witness): 1 sender + 1 receiver, each with a cached
/// part, and a preprocessed + 1..3 cached parts AIR.
#[test]
fn nv_prep_cached() {
    let e = engine();
    let (vk, proof) = CachedFixture11::new(e.config().clone()).keygen_and_prove(&e);
    assert_eq!(n_commits(&proof), 3);
    let b = honest(&vk, &proof);
    println!("NV_PREP cached11 rows={}", b.instrs.len());
    debug(&vk, &proof, 16);
    // a cached commitment tampered with in the proof: transcript and Merkle root
    let mut bad = proof.clone();
    bad.trace_vdata[0].as_mut().unwrap().cached_commitments[0][0] ^= 1;
    let b = program(&vk, &bad);
    assert!(b.failures.iter().any(|f| f == "merkle root"), "{:?}", b.failures);
    must_fail("tampered cached commitment (circuit)", || debug(&vk, &bad, 16));
    for parts in [1, 3] {
        let fx = PreprocessedAndCachedFixture::new(sels(0), e.config().clone(), parts);
        let (vk, proof) = fx.keygen_and_prove(&e);
        assert_eq!(n_commits(&proof), 2 + parts);
        let b = honest(&vk, &proof);
        println!("NV_PREP preprocessed+{parts} cached rows={}", b.instrs.len());
        debug(&vk, &proof, 16);
    }
}

/// O-2: a child with more than one commitment must run round 0 on Johnson. The program
/// generator applies the native proof-shape rule (a static fact of the child vk): a preprocessed
/// child under a first-order round 0 is refused; under Johnson round 0 it verifies.
#[test]
fn nv_prep_o2_round0() {
    use openvm_stark_backend::{AgreementTable, CertSet};
    let base = child_params_small();
    let (lb, lh) = (base.log_blowup, base.l_skip + base.n_stack);
    let bits = 5 + base.whir.query_phase_pow_bits;
    let codes = base.whir.round_codes(lb, lh);
    let kr = base.whir.k_rounds();
    let (n0, k0) = codes[0];
    let a0 = AgreementTable::first_order_agree(n0, k0, 50, 64);
    let certs: CertSet = (0..=kr[0]).map(|s| (n0 >> s, k0 >> s, (a0 + (1 << s) - 1) >> s)).collect();
    let mk = |commits: usize| {
        let mut p = base.clone();
        p.whir = p.whir.clone().with_first_order(lb, lh, bits, 50, 64, Some(&certs), commits);
        p
    };
    let fx = PreprocessedFibFixture::new(0, 1, sels(0));
    let e2 = Sha384CpuEngine::new(mk(2));
    let (vk, proof) = fx.keygen_and_prove(&e2);
    e2.verify(&vk, &proof).unwrap();
    let b = program(&vk, &proof);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    let e1 = Sha384CpuEngine::new(mk(1));
    let (vk1, proof1) = fx.keygen_and_prove(&e1);
    must_fail("first-order round 0 with a preprocessed child", || {
        program(&vk1, &proof1);
    });
}

/// Copy of `faithful_tr_tests::mutate_elem` (private there) plus the cached commitments
/// (`trace_vdata[a].cached_commitments`), the only proof elements a cached child adds.
fn mutate_elem(p: &mut Pf, k: usize) -> Option<String> {
    let mut i = 0usize;
    macro_rules! ef { ($x:expr, $l:expr) => {{ if i == k { $x += EF::ONE; return Some($l); } i += 1; }}; }
    macro_rules! ff { ($x:expr, $l:expr) => {{ if i == k { $x += F::ONE; return Some($l); } i += 1; }}; }
    macro_rules! dg { ($x:expr, $l:expr) => {{ for w in 0..6 { if i == k { $x[w] ^= 1 << (w * 7 % 64); return Some(format!("{} word {w}", $l)); } i += 1; } }}; }
    dg!(p.common_main_commit, "common_main_commit".to_string());
    for a in 0..p.trace_vdata.len() {
        if let Some(v) = p.trace_vdata[a].as_mut() {
            for c in 0..v.cached_commitments.len() {
                dg!(v.cached_commitments[c], format!("trace_vdata[{a}].cached_commitments[{c}]"));
            }
        }
    }
    for a in 0..p.public_values.len() {
        for j in 0..p.public_values[a].len() {
            ff!(p.public_values[a][j], format!("public_values[{a}][{j}]"));
        }
    }
    let g = &mut p.gkr_proof;
    ff!(g.logup_pow_witness, "gkr.logup_pow_witness".into());
    ef!(g.q0_claim, "gkr.q0_claim".into());
    for l in 0..g.claims_per_layer.len() {
        ef!(g.claims_per_layer[l].p_xi_0, format!("gkr.layer[{l}].p_xi_0"));
        ef!(g.claims_per_layer[l].p_xi_1, format!("gkr.layer[{l}].p_xi_1"));
        ef!(g.claims_per_layer[l].q_xi_0, format!("gkr.layer[{l}].q_xi_0"));
        ef!(g.claims_per_layer[l].q_xi_1, format!("gkr.layer[{l}].q_xi_1"));
    }
    for a in 0..g.sumcheck_polys.len() {
        for b in 0..g.sumcheck_polys[a].len() {
            for c in 0..3 {
                ef!(g.sumcheck_polys[a][b][c], format!("gkr.sumcheck_polys[{a}][{b}][{c}]"));
            }
        }
    }
    let bc = &mut p.batch_constraint_proof;
    for a in 0..bc.numerator_term_per_air.len() {
        ef!(bc.numerator_term_per_air[a], format!("bc.numerator[{a}]"));
    }
    for a in 0..bc.denominator_term_per_air.len() {
        ef!(bc.denominator_term_per_air[a], format!("bc.denominator[{a}]"));
    }
    for a in 0..bc.univariate_round_coeffs.len() {
        ef!(bc.univariate_round_coeffs[a], format!("bc.univariate[{a}]"));
    }
    for a in 0..bc.sumcheck_round_polys.len() {
        for b in 0..bc.sumcheck_round_polys[a].len() {
            ef!(bc.sumcheck_round_polys[a][b], format!("bc.sumcheck[{a}][{b}]"));
        }
    }
    for a in 0..bc.column_openings.len() {
        for b in 0..bc.column_openings[a].len() {
            for c in 0..bc.column_openings[a][b].len() {
                ef!(bc.column_openings[a][b][c], format!("bc.column_openings[{a}][{b}][{c}]"));
            }
        }
    }
    let sp = &mut p.stacking_proof;
    for a in 0..sp.univariate_round_coeffs.len() {
        ef!(sp.univariate_round_coeffs[a], format!("stacking.univariate[{a}]"));
    }
    for a in 0..sp.sumcheck_round_polys.len() {
        for b in 0..2 {
            ef!(sp.sumcheck_round_polys[a][b], format!("stacking.sumcheck[{a}][{b}]"));
        }
    }
    for a in 0..sp.stacking_openings.len() {
        for b in 0..sp.stacking_openings[a].len() {
            ef!(sp.stacking_openings[a][b], format!("stacking.openings[{a}][{b}]"));
        }
    }
    let w = &mut p.whir_proof;
    ff!(w.mu_pow_witness, "whir.mu_pow_witness".into());
    for a in 0..w.whir_sumcheck_polys.len() {
        for b in 0..2 {
            ef!(w.whir_sumcheck_polys[a][b], format!("whir.sumcheck[{a}][{b}]"));
        }
    }
    for a in 0..w.codeword_commits.len() {
        dg!(w.codeword_commits[a], format!("whir.codeword_commits[{a}]"));
    }
    for a in 0..w.ood_values.len() {
        ef!(w.ood_values[a], format!("whir.ood[{a}]"));
    }
    for a in 0..w.folding_pow_witnesses.len() {
        ff!(w.folding_pow_witnesses[a], format!("whir.folding_pow[{a}]"));
    }
    for a in 0..w.query_phase_pow_witnesses.len() {
        ff!(w.query_phase_pow_witnesses[a], format!("whir.query_pow[{a}]"));
    }
    for t in 0..w.initial_round_opened_rows.len() {
        for q in 0..w.initial_round_opened_rows[t].len() {
            for j in 0..w.initial_round_opened_rows[t][q].len() {
                for c in 0..w.initial_round_opened_rows[t][q][j].len() {
                    ff!(w.initial_round_opened_rows[t][q][j][c], format!("whir.initial_rows[{t}][{q}][{j}][{c}]"));
                }
            }
        }
    }
    for t in 0..w.initial_round_merkle_proofs.len() {
        for q in 0..w.initial_round_merkle_proofs[t].len() {
            for l in 0..w.initial_round_merkle_proofs[t][q].len() {
                dg!(w.initial_round_merkle_proofs[t][q][l], format!("whir.initial_merkle[{t}][{q}][{l}]"));
            }
        }
    }
    for r in 0..w.codeword_opened_values.len() {
        for q in 0..w.codeword_opened_values[r].len() {
            for j in 0..w.codeword_opened_values[r][q].len() {
                ef!(w.codeword_opened_values[r][q][j], format!("whir.codeword_values[{r}][{q}][{j}]"));
            }
        }
    }
    for r in 0..w.codeword_merkle_proofs.len() {
        for q in 0..w.codeword_merkle_proofs[r].len() {
            for l in 0..w.codeword_merkle_proofs[r][q].len() {
                dg!(w.codeword_merkle_proofs[r][q][l], format!("whir.codeword_merkle[{r}][{q}][{l}]"));
            }
        }
    }
    for a in 0..w.final_poly.len() {
        ef!(w.final_poly[a], format!("whir.final_poly[{a}]"));
    }
    let _ = i;
    None
}


/// Program ≡ native on every single-element mutation of a child with preprocessed / cached
/// traces (FAITHFUL §2(d)(iii) `nv_tr_every_proof_element`, extended): for each value element the
/// native verifier accepts iff the NV program records no failure. Fixtures: preprocessed Fib,
/// preprocessed + 2 cached parts, the toy base (Split: 2 preprocessed AIRs); 3 lever sets.
#[test]
fn nv_prep_every_proof_element() {
    use crate::sha384::e2e_tests::with_levers;
    use openvm_stark_backend::WhirLevers;
    let base = WhirLevers::default();
    let cases: Vec<(&str, WhirLevers, usize)> = vec![
        ("default", base, 1),
        ("x15+multiproof+whir_y+widepow", WhirLevers { multiproof: true, whir_y: true, wide_query_pow: true, ..base }, 15),
        ("gruen+derive+mask+k1", WhirLevers { gruen_gkr: true, gkr_derive_claims: true, gruen_zerocheck: true, next_mask: true, k_first: 1, ..base }, 1),
    ];
    let mut mismatches = vec![];
    for (name, lv, x15) in cases {
        let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 8, 3);
        p.max_constraint_degree = 4;
        let p = with_levers(p, lv, x15, 5);
        let engine = Sha384CpuEngine::new(p);
        for fx in 0..3 {
            let (vk, proof) = match fx {
                0 => PreprocessedFibFixture::new(0, 1, sels(0)).keygen_and_prove(&engine),
                1 => PreprocessedAndCachedFixture::new(sels(0), engine.config().clone(), 2).keygen_and_prove(&engine),
                _ => super::prep_demo::ToyBase { v: super::prep_demo::Variant::Split, n: 16, steps: 16, exec_rows: 32, seed: 1 }.keygen_and_prove(&engine),
            };
            let (mut n, mut both_reject, mut both_accept) = (0, 0, 0);
            for k in 0.. {
                let mut bad = proof.clone();
                let Some(label) = mutate_elem(&mut bad, k) else { break };
                n += 1;
                let mut t = ShaTranscript::default();
                let native_ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    openvm_stark_backend::verifier::verify(engine.config(), &vk, &bad, &mut t).is_ok()
                }))
                .unwrap_or(false);
                let prog_ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| program(&vk, &bad).failures.is_empty())).unwrap_or(false);
                match (native_ok, prog_ok) {
                    (false, false) => both_reject += 1,
                    (true, true) => both_accept += 1,
                    _ => mismatches.push(format!("{name} fx{fx} {label}: native_ok={native_ok} program_ok={prog_ok}")),
                }
            }
            println!("NV_PREP_ELEMENTS {name} fixture={fx} elements={n} both_reject={both_reject} both_accept={both_accept}");
        }
    }
    for m in &mismatches {
        println!("NV_PREP_ELEMENT_MISMATCH {m}");
    }
    assert!(mismatches.is_empty(), "{} program/native mismatches", mismatches.len());
}

