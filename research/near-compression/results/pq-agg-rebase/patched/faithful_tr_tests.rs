//! NV-faithful audit, parts (d) transcript/sampling and (e) Merkle openings: tamper tests.
//! Each `must_fail` case is a cheating trace (or a cheating witness generated through a
//! test-only hook in the verifier program) that the circuit must reject.
use core::borrow::BorrowMut;

use openvm_stark_backend::{test_utils::{FibFixture, TestFixture}, StarkEngine};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;

use super::{
    transcript2::{Hash2Cols, Samp2Cols, HASH2_WIDTH, SAMP2_WIDTH},
    uair::N_COMMON,
};
use crate::sha384::{config::*, e2e_tests::child_params_small};

type Vk = openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<Sha384Config>;
type Pf = openvm_stark_backend::proof::Proof<Sha384Config>;

/// NvAir common-column flags.
const KG: usize = 2;
const KH: usize = 3;
const KS: usize = 4;

fn debug_params() -> openvm_stark_backend::SystemParams {
    let mut p = crate::sha384::e2e_tests::parent_params_debug();
    p.max_constraint_degree = super::circuit::NvCircuit::new(3, 16, 1).layout().degree().max(6);
    p
}

/// Generate the NV traces for (vk, proof), apply `mutate`, run the debug constraint + bus check.
fn check(vk: &Vk, proof: &Pf, log_rows: usize, mutate: impl FnOnce(&mut Vec<RowMajorMatrix<F>>)) {
    use openvm_cpu_backend::CpuBackend;
    use openvm_stark_backend::prover::{AirProvingContext, ProvingContext};
    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), log_rows, 1);
    let airs = circ.airs::<Sha384Config>();
    let (mut mats, _b) = circ.generate(vk, proof);
    let pv = _b.public_values();
    mutate(&mut mats);
    let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = mats
        .into_iter()
        .enumerate()
        .map(|(i, m)| if i == 0 { AirProvingContext::simple(m, pv.clone()) } else { AirProvingContext::simple_no_pis(m) })
        .collect();
    Sha384CpuEngine::new(debug_params()).debug(&airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
}

fn must_fail(name: &str, f: impl FnOnce()) {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    assert!(r.is_err(), "tamper `{name}` accepted");
    println!("NV_TR_TAMPER_REJECTED {name}");
}

fn rows_with(m: &RowMajorMatrix<F>, flag: usize) -> Vec<usize> {
    (0..m.values.len() / m.width).filter(|&r| m.values[r * m.width + flag] == F::ONE).collect()
}
fn hash_row(m: &mut RowMajorMatrix<F>, r: usize) -> &mut Hash2Cols<F> {
    let w = m.width;
    m.values[r * w + N_COMMON..r * w + N_COMMON + HASH2_WIDTH].borrow_mut()
}
fn samp_row(m: &mut RowMajorMatrix<F>, r: usize) -> &mut Samp2Cols<F> {
    let w = m.width;
    m.values[r * w + N_COMMON..r * w + N_COMMON + SAMP2_WIDTH].borrow_mut()
}
/// GLUE `job` column (pool offset 1).
fn glue_job(m: &mut RowMajorMatrix<F>, r: usize) -> &mut F {
    let w = m.width;
    &mut m.values[r * w + N_COMMON + 1]
}

/// Rename every occurrence of transcript job id `from` to `to` (hash row, predecessor's `nxt`,
/// sample rows, GLUE rows): an internally consistent relabeling of one squeeze job.
fn rename_job(m: &mut RowMajorMatrix<F>, from: F, to: F) {
    for r in rows_with(m, KH) {
        let h = hash_row(m, r);
        if h.job == from {
            h.job = to;
        }
        if h.nxt == from {
            h.nxt = to;
        }
    }
    for r in rows_with(m, KS) {
        let s = samp_row(m, r);
        if s.job == from {
            s.job = to;
        }
    }
    for r in rows_with(m, KG) {
        let j = glue_job(m, r);
        if *j == from {
            *j = to;
        }
    }
}

fn fib() -> (Vk, Pf) {
    let engine = Sha384CpuEngine::new(child_params_small());
    FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine)
}

fn squeeze_rows(m: &mut RowMajorMatrix<F>) -> Vec<usize> {
    rows_with(m, KH).into_iter().filter(|&r| hash_row(m, r).op_s == F::ONE).collect()
}

/// Bug B1 (fixed): squeeze job ids were free witnesses.  Giving squeeze job #1 the id of squeeze
/// job #0 makes two GLUE jobs, two sample runs and two hash rows share one id; the slot (state
/// unit), word and digest buses then only constrain the *union* of their messages, so state words
/// can be mixed between the two jobs (the hashed state is no longer the chain state).  Before
/// the fix this relabeled trace was accepted; now `job = TJOB_SQUEEZE_BASE + #squeezes before`.
#[test]
fn nv_tr_squeeze_id_collision() {
    let (vk, proof) = fib();
    check(&vk, &proof, 16, |_| {});
    must_fail("squeeze job id collision", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let sq = squeeze_rows(m);
            assert!(sq.len() >= 2);
            let j0 = hash_row(m, sq[0]).job;
            let j1 = hash_row(m, sq[1]).job;
            rename_job(m, j1, j0);
        })
    });
    must_fail("squeeze job renamed (fresh id)", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let sq = squeeze_rows(m);
            let j1 = hash_row(m, sq[1]).job;
            rename_job(m, j1, F::from_u32(super::transcript2::TJOB_SQUEEZE_BASE + 100_000));
        })
    });
}

/// Bug B2 (fixed): the op of a static transcript job (flush / commit) was not bound to the
/// program; the anchor now carries the tag (ALU `Anchor` P3 = tag, hash row receives its tag).
/// Here a commit row is relabeled as a flush (everything else unchanged).
#[test]
fn nv_tr_anchor_tag() {
    let (vk, proof) = fib();
    must_fail("commit relabeled as flush", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let r = rows_with(m, KH).into_iter().find(|&r| hash_row(m, r).op_c == F::ONE).unwrap();
            let h = hash_row(m, r);
            h.op_c = F::ZERO;
            h.op_f = F::ONE;
        })
    });
}

/// Hash-chain / sample-role tamper classes.
#[test]
fn nv_tr_tamper() {
    let (vk, proof) = fib();
    // reorder two consecutive static jobs (swap their rows, keep the nxt links consistent)
    must_fail("reorder transcript jobs", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let hr = rows_with(m, KH);
            let i = (1..hr.len() - 2)
                .find(|&i| hash_row(m, hr[i]).op_s == F::ZERO && hash_row(m, hr[i + 1]).op_s == F::ZERO)
                .expect("two consecutive static jobs");
            let (a, b) = (hr[i], hr[i + 1]);
            let w = m.width;
            let ra: Vec<F> = m.values[a * w + N_COMMON..(a + 1) * w].to_vec();
            let rb: Vec<F> = m.values[b * w + N_COMMON..(b + 1) * w].to_vec();
            m.values[a * w + N_COMMON..(a + 1) * w].copy_from_slice(&rb);
            m.values[b * w + N_COMMON..(b + 1) * w].copy_from_slice(&ra);
            // relink: prev -> b' -> a' -> next
            let (ja, jb) = (hash_row(m, b).job, hash_row(m, a).job);
            let nxt_after = hash_row(m, a).nxt;
            hash_row(m, hr[i - 1]).nxt = jb;
            hash_row(m, a).nxt = ja;
            hash_row(m, b).nxt = nxt_after;
            let ts = hash_row(m, hr[i - 1]).t_start + hash_row(m, hr[i - 1]).cnt;
            hash_row(m, a).t_start = ts;
            let ts2 = ts + hash_row(m, a).cnt;
            hash_row(m, b).t_start = ts2;
        })
    });
    // anchor (t_start, cnt) of a static job shifted
    must_fail("anchor t_start shifted", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let r = rows_with(m, KH).into_iter().find(|&r| hash_row(m, r).op_f == F::ONE).unwrap();
            hash_row(m, r).t_start += F::ONE;
        })
    });
    must_fail("anchor cnt changed", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let r = rows_with(m, KH).into_iter().find(|&r| hash_row(m, r).op_f == F::ONE).unwrap();
            hash_row(m, r).cnt += F::ONE;
        })
    });
    // sample from the wrong tidx: a squeeze job and its sample run shifted by one
    must_fail("samples at shifted tidx", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let sq = squeeze_rows(m);
            let j = hash_row(m, sq[1]).job;
            hash_row(m, sq[1]).t_start += F::ONE;
            for r in rows_with(m, KS) {
                let s = samp_row(m, r);
                if s.job == j {
                    s.t_job += F::ONE;
                }
            }
        })
    });
    // skip candidate 1 on a non-last sample row
    must_fail("sample candidate skipped", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let r = rows_with(m, KS).into_iter().find(|&r| samp_row(m, r).is_last == F::ZERO).unwrap();
            samp_row(m, r).h1 = F::ZERO;
        })
    });
    // a rejected candidate declared accepted (acc flipped, gadgets left)
    must_fail("sample acceptance flipped", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let r = rows_with(m, KS)[0];
            let s = samp_row(m, r);
            s.acc[0] = F::ONE - s.acc[0];
        })
    });
    // read fewer state words (rdw prefix shortened) on a squeeze row
    must_fail("squeeze reads fewer words", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let r = squeeze_rows(m)[0];
            let h = hash_row(m, r);
            let lw = h.last_word.as_canonical_u32() as usize;
            if lw > 0 {
                h.rdw[lw] = F::ZERO;
                h.last_word -= F::ONE;
            } else {
                h.rdw[0] = F::ZERO;
            }
        })
    });
    // an extra squeeze row is impossible without a row; a flush declared last (hn = 0)
    must_fail("chain cut (hn = 0 mid-chain)", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let r = rows_with(m, KH)[2];
            hash_row(m, r).hn = F::ZERO;
        })
    });
}

/// PoW (tag 7): the free coefficients c[3..12] of the `PowChk` cell are forced to zero by the
/// program's comparison; a forged output word or BIT row is rejected.
#[test]
fn nv_tr_pow_tamper() {
    use super::isa::{Op, OP_LO};
    let (vk, proof) = fib();
    let find_op = |m: &RowMajorMatrix<F>, op: Op| -> Vec<usize> {
        let w = m.width;
        let h_off = N_COMMON + core::mem::offset_of!(super::uair::AbCols<u8>, h);
        let g_off = N_COMMON + core::mem::offset_of!(super::uair::AbCols<u8>, g);
        let _ = OP_LO;
        let v = op as usize;
        (0..m.values.len() / w)
            .filter(|&r| m.values[r * w] == F::ONE && m.values[r * w + h_off + v % OP_LO] == F::ONE && m.values[r * w + g_off + v / OP_LO] == F::ONE)
            .collect()
    };
    check(&vk, &proof, 16, |mats| assert!(!find_op(&mats[0], Op::PowChk).is_empty(), "fixture has no PoW"));
    must_fail("PowChk free coefficient c[3]", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let r = find_op(m, Op::PowChk)[0];
            let w = m.width;
            m.values[r * w + super::uair::U_C + 3] += F::ONE;
        })
    });
    must_fail("PoW output word limb 1 (hash row)", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let r = rows_with(m, KH).into_iter().find(|&r| hash_row(m, r).op_p == F::ONE).unwrap();
            hash_row(m, r).state_out[1] += F::ONE;
        })
    });
    must_fail("PoW LoadBit row value", || {
        check(&vk, &proof, 16, |mats| {
            let m = &mut mats[0];
            let r = find_op(m, Op::PowChk)[0];
            // the first LoadBit after the PowChk row recomposes limb 1
            let lb = find_op(m, Op::LoadBit).into_iter().find(|&x| x > r).unwrap();
            let w = m.width;
            let c = &mut m.values[lb * w + super::uair::U_C];
            *c = F::ONE - *c;
        })
    });
}

/// Witness-level attacks generated through the verifier program's test hooks: the program is
/// run with a cheating witness choice (all other cells consistent); the circuit must reject.
#[test]
fn nv_tr_hook_tamper() {
    use super::verifier::{set_tamper, Tamper};
    let (vk, proof) = fib();
    for t in [Tamper::NonCanonicalIndex, Tamper::MerkleSwapLr, Tamper::OtherLeaf, Tamper::IndexBitFlip] {
        let name = format!("{t:?}");
        must_fail(&name, || {
            set_tamper(t);
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| check(&vk, &proof, 16, |_| {})));
            let hit = super::verifier::tamper_hit();
            set_tamper(Tamper::None);
            assert!(hit, "tamper {t:?} found no applicable query");
            if let Err(e) = r {
                std::panic::resume_unwind(e);
            }
        });
    }
}

/// x15 domain: the decomposition x >> m = 15 q + a with a = 15 (q - 1) must be rejected, as
/// must a non-canonical index.
#[test]
fn nv_tr_x15_hook_tamper() {
    use super::verifier::{set_tamper, Tamper};
    use crate::sha384::e2e_tests::with_levers;
    let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 8, 3);
    p.max_constraint_degree = 4;
    let p = with_levers(p, openvm_stark_backend::WhirLevers { multiproof: true, ..Default::default() }, 15, 5);
    let engine = Sha384CpuEngine::new(p);
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    check(&vk, &proof, 16, |_| {});
    for t in [Tamper::X15AEquals15, Tamper::MerkleSwapLr, Tamper::OtherLeaf] {
        let name = format!("x15 {t:?}");
        must_fail(&name, || {
            set_tamper(t);
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| check(&vk, &proof, 16, |_| {})));
            let hit = super::verifier::tamper_hit();
            set_tamper(Tamper::None);
            assert!(hit, "tamper {t:?} found no applicable query");
            if let Err(e) = r {
                std::panic::resume_unwind(e);
            }
        });
    }
}

/// Transcript schedule equals the native verifier's (end state) for every in-circuit lever, and
/// the program is independent of the proof values.  Run once at default SHA levers and once with
/// NEARPROOF_DIGEST_BYTES=42 NEARPROOF_COSET_LEAF=1.
#[test]
fn nv_tr_native_schedule_levers() {
    use crate::sha384::e2e_tests::with_levers;
    use openvm_stark_backend::{test_utils::InteractionsFixture11, StarkEngine, WhirLevers};
    let base = WhirLevers::default();
    let cases: Vec<(&str, WhirLevers, usize)> = vec![
        ("default", base, 1),
        ("whir_y", WhirLevers { whir_y: true, ..base }, 1),
        ("x15+multiproof", WhirLevers { multiproof: true, ..base }, 15),
        ("wide pow+k1+keep", WhirLevers { wide_query_pow: true, k_first: 1, keep_domain: true, ..base }, 1),
        ("gruen+derive+mask", WhirLevers { gruen_gkr: true, gkr_derive_claims: true, gruen_zerocheck: true, next_mask: true, ..base }, 1),
        ("tight+x15", WhirLevers { tight_heights: true, whir_y: true, ..base }, 15),
    ];
    for (name, lv, x15) in cases {
        let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 8, 3);
        p.max_constraint_degree = 4;
        let p = with_levers(p, lv, x15, 5);
        let engine = Sha384CpuEngine::new(p);
        for fx in 0..2 {
            let run = || {
                let (vk, pr) = if fx == 0 { FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine) } else { InteractionsFixture11.keygen_and_prove(&engine) };
                engine.verify(&vk, &pr).unwrap();
                let mut b = super::builder::Builder::new(17, 0);
                super::verifier::build_verifier(&mut b, &vk, &pr);
                assert!(b.failures.is_empty(), "{name}: {:?}", b.failures);
                let mut t = ShaTranscript::default();
                openvm_stark_backend::verifier::verify(engine.config(), &vk, &pr, &mut t).unwrap();
                assert_eq!(t.state, b.transcript.inner.state, "{name}: transcript diverged from native");
                b
            };
            let (b1, b2) = (run(), run());
            assert_eq!(b1.instrs, b2.instrs, "{name}: program depends on proof values");
            println!("NV_TR_SCHEDULE {name} fixture={fx} levers={:?} ok rows={}", sha_levers(), b1.instrs.len());
        }
    }
}

/// Mutate the `k`-th value element of the proof (fixed traversal order; EF/F += 1, digest word
/// bit 0 flipped); returns its label, or None past the last element.  Shape fields untouched.
fn mutate_elem(p: &mut Pf, k: usize) -> Option<String> {
    let mut i = 0usize;
    macro_rules! ef { ($x:expr, $l:expr) => {{ if i == k { $x += EF::ONE; return Some($l); } i += 1; }}; }
    macro_rules! ff { ($x:expr, $l:expr) => {{ if i == k { $x += F::ONE; return Some($l); } i += 1; }}; }
    macro_rules! dg { ($x:expr, $l:expr) => {{ for w in 0..6 { if i == k { $x[w] ^= 1 << (w * 7 % 64); return Some(format!("{} word {w}", $l)); } i += 1; } }}; }
    dg!(p.common_main_commit, "common_main_commit".to_string());
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

/// Program ≡ native on every single-element mutation of the proof: for each value element the
/// native verifier accepts iff the NV program records no failure (every program failure is a
/// `Zero` row / Merkle root comparison in-circuit).  This is the "no native check skipped, no
/// proof element left unconsumed" test.
#[test]
fn nv_tr_every_proof_element() {
    use crate::sha384::e2e_tests::with_levers;
    use openvm_stark_backend::{test_utils::InteractionsFixture11, WhirLevers};
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
        for fx in 0..2 {
            let (vk, proof) = if fx == 0 { FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine) } else { InteractionsFixture11.keygen_and_prove(&engine) };
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
                let prog_ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut b = super::builder::Builder::new(17, 0);
                    super::verifier::build_verifier(&mut b, &vk, &bad);
                    b.failures.is_empty()
                }))
                .unwrap_or(false);
                match (native_ok, prog_ok) {
                    (false, false) => both_reject += 1,
                    (true, true) => both_accept += 1,
                    _ => mismatches.push(format!("{name} fx{fx} {label}: native_ok={native_ok} program_ok={prog_ok}")),
                }
            }
            println!("NV_TR_ELEMENTS {name} fixture={fx} elements={n} both_reject={both_reject} both_accept={both_accept}");
        }
    }
    for m in &mismatches {
        println!("NV_TR_ELEMENT_MISMATCH {m}");
    }
    assert!(mismatches.is_empty(), "{} program/native mismatches", mismatches.len());
}

/// Bug B3 (fix: `LoadF` op, base-field loads with c1..c11 = 0 — made on the coordinator's tree):
/// `Builder::pow` recomposes PoW output word 0 as load_f(l0) + x1 X + x2 X^2 and compares it with
/// the `PowChk` cell; `load_f` was a plain `Load` (all 12 coefficients free), so coefficients 1, 2
/// of the l0 cell absorb any non-zero top bits and the leading-zero check is vacuous.
/// Setup: the child is proved with mu PoW bits b; the verifying key claims b + 16 bits (the PoW
/// job's hash does not depend on the bit count and `pre_hash` is unchanged, so the transcript is
/// identical) — the native verifier rejects, the honest program fails exactly at the PoW check,
/// and the hook fills the l0 cell's coefficients 1, 2.  Fails (= trace accepted) without B3's fix.
#[test]
fn nv_tr_pow_free_limb() {
    use super::verifier::{set_tamper, Tamper};
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let mut vk2 = vk.clone();
    vk2.inner.params.whir.mu_pow_bits += 16;
    let e2 = Sha384CpuEngine::new(vk2.inner.params.clone());
    let mut t = ShaTranscript::default();
    assert!(openvm_stark_backend::verifier::verify(e2.config(), &vk2, &proof, &mut t).is_err(), "native accepts");
    let mut b = super::builder::Builder::new(17, 0);
    super::verifier::build_verifier(&mut b, &vk2, &proof);
    assert!(b.failures.iter().all(|f| f.starts_with("pow")) && !b.failures.is_empty(), "{:?}", b.failures);
    must_fail("PoW below the claimed bits, low-limb cell absorbs top bits", || {
        set_tamper(Tamper::PowFreeLimb);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| check(&vk2, &proof, 16, |_| {})));
        let hit = super::verifier::tamper_hit();
        set_tamper(Tamper::None);
        assert!(hit);
        if let Err(e) = r {
            std::panic::resume_unwind(e);
        }
    });
}
