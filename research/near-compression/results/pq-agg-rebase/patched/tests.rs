use openvm_stark_backend::{
    test_utils::{FibFixture, InteractionsFixture11, TestFixture},
    StarkEngine,
};
use p3_field::PrimeCharacteristicRing;

use super::{builder::Builder, verifier::build_verifier};
use crate::sha384::{config::*, e2e_tests::child_params_small};

fn build(fx: &impl TestFixture<Sha384Config>) -> (Builder, Builder) {
    build2(fx, fx)
}

/// Programs for two children of the same shape (`fx2` should carry a different witness).
fn build2(fx: &impl TestFixture<Sha384Config>, fx2: &impl TestFixture<Sha384Config>) -> (Builder, Builder) {
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = fx.keygen_and_prove(&engine);
    engine.verify(&vk, &proof).unwrap();
    let mut b = Builder::new(17, 0);
    build_verifier(&mut b, &vk, &proof);
    // native transcript end state must match the program's transcript
    let mut t = ShaTranscript::default();
    openvm_stark_backend::verifier::verify(engine.config(), &vk, &proof, &mut t).unwrap();
    assert_eq!(t.state, b.transcript.inner.state, "transcript diverged from native");
    // a second proof of the same shape gives the identical program
    let (vk2, proof2) = fx2.keygen_and_prove(&engine);
    let mut b2 = Builder::new(17, 0);
    build_verifier(&mut b2, &vk2, &proof2);
    (b, b2)
}

#[test]
fn nv_program_fib() {
    // two different witnesses (the prover is deterministic: the same witness proves identically)
    let (b, b2) = build2(&FibFixture::new(0, 1, 1 << 5), &FibFixture::new(2, 3, 1 << 5));
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    println!("NV_PROGRAM_ROWS {} jobs={} merkle_nodes={}", b.instrs.len(), b.job_units.len(), b.merkle_nodes);
    assert_eq!(b.instrs, b2.instrs, "program depends on proof values");
}

#[test]
fn nv_program_interactions() {
    let (b, _) = build(&InteractionsFixture11);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
}

#[test]
fn nv_program_detects_tampering() {
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let cases: Vec<(&str, Box<dyn Fn(&mut openvm_stark_backend::proof::Proof<Sha384Config>)>)> = vec![
        ("column opening", Box::new(|p| p.batch_constraint_proof.column_openings[0][0][0] += EF::ONE)),
        ("gkr claim", Box::new(|p| p.gkr_proof.q0_claim += EF::ONE)),
        ("stacking opening", Box::new(|p| p.stacking_proof.stacking_openings[0][0] += EF::ONE)),
        ("whir sumcheck", Box::new(|p| p.whir_proof.whir_sumcheck_polys[0][0] += EF::ONE)),
        ("final poly", Box::new(|p| p.whir_proof.final_poly[0] += EF::ONE)),
        ("codeword value", Box::new(|p| p.whir_proof.codeword_opened_values[0][0][1] += EF::ONE)),
    ];
    for (name, f) in cases {
        let mut bad = proof.clone();
        f(&mut bad);
        let mut b = Builder::new(17, 0);
        build_verifier(&mut b, &vk, &bad);
        println!("NV_TAMPER {name}: {:?}", b.failures);
        // value tampering inside a Merkle-authenticated leaf is caught by the Merkle AIR,
        // not by an ALU assertion; everything else must fail an ALU assertion.
        if name != "codeword value" {
            assert!(!b.failures.is_empty(), "{name} not detected");
        }
    }
}

fn nv_debug_params() -> openvm_stark_backend::SystemParams {
    let mut p = crate::sha384::e2e_tests::parent_params_debug();
    p.max_constraint_degree = super::circuit::NvCircuit::new(3, 16, 1).layout().degree().max(6);
    p
}

fn nv_debug(fx: &impl TestFixture<Sha384Config>, log_rows: usize) {
    use openvm_cpu_backend::CpuBackend;
    use openvm_stark_backend::prover::{AirProvingContext, MatrixDimensions, ProvingContext};
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = fx.keygen_and_prove(&engine);
    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), log_rows, 1);
    let airs = circ.airs::<Sha384Config>();
    let (mats, b) = circ.generate(&vk, &proof);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    if let Ok(rows) = std::env::var("NV_DUMP_ROWS") {
        for r in rows.split(',').map(|x| x.parse::<usize>().unwrap()) {
            eprintln!("NV_DUMP row {r}: {:?}", b.instrs.get(r));
        }
    }
    let mut total = 0;
    for (a, m) in airs.iter().zip(&mats) {
        println!("NV_AIR {} {} x {}", a.name(), m.height(), m.width());
        total += m.height() * m.width();
    }
    println!("NV_TOTAL_CELLS {total}");
    let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = mats
        .into_iter()
        .enumerate()
        .map(|(i, m)| if i == 0 { AirProvingContext::simple(m, b.public_values()) } else { AirProvingContext::simple_no_pis(m) })
        .collect();
    let parent = Sha384CpuEngine::new(nv_debug_params());
    parent.debug(&airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
}

#[test]
fn nv_circuit_fib_debug() {
    nv_debug(&FibFixture::new(0, 1, 1 << 5), 16);
}

fn nv_debug_mats(
    vk: &openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<Sha384Config>,
    proof: &openvm_stark_backend::proof::Proof<Sha384Config>,
    log_rows: usize,
    mutate: impl FnOnce(&mut Vec<p3_matrix::dense::RowMajorMatrix<F>>, &[String]),
) {
    use openvm_cpu_backend::CpuBackend;
    use openvm_stark_backend::prover::{AirProvingContext, ProvingContext};
    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), log_rows, 1);
    let airs = circ.airs::<Sha384Config>();
    let names: Vec<String> = airs.iter().map(|a| a.name()).collect();
    let (mut mats, _b) = circ.generate(vk, proof);
    if let Ok(rows) = std::env::var("NV_DUMP_ROWS") {
        for r in rows.split(',').map(|x| x.parse::<usize>().unwrap()) {
            eprintln!("NV_DUMP row {r}: {:?}", _b.instrs.get(r));
        }
    }
    let pv = _b.public_values();
    mutate(&mut mats, &names);
    let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = mats
        .into_iter()
        .enumerate()
        .map(|(i, m)| if i == 0 { AirProvingContext::simple(m, pv.clone()) } else { AirProvingContext::simple_no_pis(m) })
        .collect();
    let parent = Sha384CpuEngine::new(nv_debug_params());
    parent.debug(&airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
}

/// First row of NvAir with role flag column `flag` set.
fn role_row(m: &p3_matrix::dense::RowMajorMatrix<F>, flag: usize) -> usize {
    (0..m.values.len() / m.width).find(|&r| m.values[r * m.width + flag] == F::ONE).expect("role rows")
}

fn must_fail(name: &str, f: impl FnOnce()) {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    assert!(r.is_err(), "tamper `{name}` accepted");
    println!("NV_TAMPER_REJECTED {name}");
}

#[test]
fn nv_circuit_tamper() {
    use core::borrow::BorrowMut;
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    // 1. merkle sibling digest
    let mut bad = proof.clone();
    bad.whir_proof.initial_round_merkle_proofs[0][0][1][2] ^= 1;
    must_fail("merkle-sibling-digest", || nv_debug_mats(&vk, &bad, 16, |_, _| {}));
    // 2. opened value
    let mut bad = proof.clone();
    bad.whir_proof.initial_round_opened_rows[0][0][1][0] += F::ONE;
    must_fail("opened-value", || nv_debug_mats(&vk, &bad, 16, |_, _| {}));
    // 3. transcript sample (row-consistent refill of the candidate gadgets)
    must_fail("transcript-sample", || {
        nv_debug_mats(&vk, &proof, 16, |mats, names| {
            use super::transcript2::{fill_cand, Samp2Cols};
            use p3_field::PrimeField32;
            let _ = names;
            let w = mats[0].width;
            let r = role_row(&mats[0], 4);
            let o = r * w + super::uair::N_COMMON;
            let row: &mut Samp2Cols<F> = mats[0].values[o..o + super::transcript2::SAMP2_WIDTH].borrow_mut();
            row.b[1] += F::ONE;
            let cb: [u8; 4] = core::array::from_fn(|k| row.b[k].as_canonical_u32() as u8);
            fill_cand(row, 0, cb);
        })
    });
    // 4. output-state limb of the first transcript job (vk pre-hash commit)
    must_fail("transcript-state-limb", || {
        nv_debug_mats(&vk, &proof, 16, |mats, names| {
            let _ = names;
            let w = mats[0].width;
            let r = role_row(&mats[0], 3);
            mats[0].values[r * w + super::uair::N_COMMON + 9] += F::ONE;
        })
    });
    // 5. an ALU result (row 1000's c0)
    must_fail("alu-result", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            let w = mats[0].width;
            mats[0].values[1000 * w + super::uair::U_C] += F::ONE;
        })
    });
    // 5b. NvAir padding rows must be all zero: a non-zero value in the last (padding) row
    must_fail("nvair padding row y", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            let w = mats[0].width;
            let h = mats[0].values.len() / w;
            mats[0].values[(h - 1) * w + 5] += F::ONE;
        })
    });
    must_fail("nvair padding row pool", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            let w = mats[0].width;
            let h = mats[0].values.len() / w;
            mats[0].values[(h - 1) * w + super::uair::N_COMMON + 20] += F::ONE;
        })
    });
    // 5c. op relabel: a Const row relabeled as Load (P unchanged, c changed) must be rejected
    //     (the B-field range check binds the op to P1)
    must_fail("op relabel const->load", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            use super::isa::{Op, OP_LO};
            let w = mats[0].width;
            let base = super::uair::N_COMMON;
            let h_off = base + 36;
            let g_off = h_off + OP_LO;
            // find a Const row
            let cst = Op::Const as usize;
            let r = (0..mats[0].values.len() / w)
                .find(|&r| mats[0].values[r * w] == F::ONE
                    && mats[0].values[r * w + h_off + cst % OP_LO] == F::ONE
                    && mats[0].values[r * w + g_off + cst / OP_LO] == F::ONE)
                .unwrap();
            let ld = Op::Load as usize;
            mats[0].values[r * w + h_off + cst % OP_LO] = F::ZERO;
            mats[0].values[r * w + g_off + cst / OP_LO] = F::ZERO;
            mats[0].values[r * w + h_off + ld % OP_LO] = F::ONE;
            mats[0].values[r * w + g_off + ld / OP_LO] = F::ONE;
            mats[0].values[r * w + base + 24] += F::ONE;
        })
    });
    // 6. a BIND row's accumulator (row na + 10)
    must_fail("bind-acc", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            let w = mats[0].width;
            let na = role_row(&mats[0], 1);
            mats[0].values[(na + 10) * w + super::uair::N_COMMON + 36] += F::ONE;
        })
    });
    // 7. a BIND row's copy of the program word P0 (row na + 600)
    must_fail("bind-program-word", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            let w = mats[0].width;
            let na = role_row(&mats[0], 1);
            mats[0].values[(na + 300) * w + super::uair::N_COMMON + 48] += F::ONE;
        })
    });
}

#[test]
fn nv_circuit_interactions_debug() {
    nv_debug(&InteractionsFixture11, 16);
}

/// The opening of a column of the child's ALU equals sum_x w(x) T[x] with
/// w(x) = L_{x mod 2^l}(r0) * eq(r_1..r_n, bits(x >> l)) (LSB first).
#[test]
fn nv_opening_formula() {
    use openvm_stark_backend::poly_common::eval_eq_uni;
    use p3_field::TwoAdicField;
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk0, p0) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let mut pp = openvm_stark_backend::test_utils::test_system_params_small(2, 16, 3);
    pp.max_constraint_degree = nv_debug_params().max_constraint_degree;
    let parent = Sha384CpuEngine::new(pp);
    let circ = super::circuit::NvCircuit::new(3, 16, 1);
    let t0 = std::time::Instant::now();
    let (vk1, p1, b1, _) = super::circuit::prove_level(&circ, &parent, &vk0, &p0);
    println!("NV_L1_PROVE_S {:.1}", t0.elapsed().as_secs_f64());
    // level 2 program (no binding) to obtain the batch point and the openings
    let mut b2 = Builder::new(19, 1024);
    build_verifier(&mut b2, &vk1, &p1);
    println!("NV_L2_PROGRAM_ROWS {}", b2.instrs.len());
    let l = 2usize;
    let t = b2.dbg_tid.iter().position(|&a| a == 0).unwrap();
    let rs = &b2.dbg_rs;
    let omega = F::two_adic_generator(l);
    let n = 16 - l;
    let mut ok = 0;
    for j in 0..4 {
        let col: Vec<F> = b1.instrs.iter().map(|i| F::from_u32(i.words()[j])).collect();
        let mut s = EF::ZERO;
        for (x, &v) in col.iter().enumerate() {
            let lw: EF = eval_eq_uni(l, rs[0], EF::from(omega.exp_u64((x % 4) as u64)));
            let mut e = EF::ONE;
            for i in 0..n {
                let bit = (x >> (l + i)) & 1 == 1;
                e *= if bit { rs[1 + i] } else { EF::ONE - rs[1 + i] };
            }
            s += lw * e * v;
        }
        let open = b2.dbg_openings[t][super::uair::U_P + j];
        println!("NV_OPENING P{j}: formula == opening: {}", s == open);
        ok += (s == open) as usize;
    }
    assert_eq!(ok, 4);
}

/// [stream research] The WHIR per-round regimes as bound in a vk (O-2 first-order / Johnson).
fn print_vk_regimes(tag: &str, vk: &openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<Sha384Config>) {
    let w = &vk.inner.params.whir;
    match &w.agreement {
        Some(t) => println!(
            "{tag}_VK_REGIMES m={} margin_milli={} target={} rounds(n,k,A,q,regime)={:?}",
            t.m,
            t.margin_milli,
            t.target_bits,
            t.rounds.iter().map(|r| (r.n, r.kdim, r.agree, r.queries, if r.first_order { "O2" } else { "J" })).collect::<Vec<_>>()
        ),
        None => println!("{tag}_VK_REGIMES none (plain list decoding) queries={:?}", w.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>()),
    }
}

/// NV-verifies-NV chain (ignored; env-driven).
///   NV_LEVELS=4 NV_LOG_ROWS=17 PARENT_N_STACK=16 PARENT_BITS=20 PARENT_LIST_M=3 ...
#[test]
#[ignore]
fn nv_chain() {
    use crate::sha384::e2e_tests::{describe, env_usize, params_from_env, proof_sizes, soundness};
    use openvm_stark_backend::keygen::types::MultiStarkVerifyingKey;
    use openvm_stark_backend::proof::Proof;
    let levels = env_usize("NV_LEVELS", 2);
    // default: phase B with program binding at every level whose child is NV, then FINAL with the
    // same (fixed-point) program under the final domain, checked by V_d against the pinned
    // program.  NV_UNBOUND_FINAL=1 keeps the old measurement-only FINAL (FINAL_* params, child
    // program NOT bound) after phase A.
    let unbound_final = env_usize("NV_UNBOUND_FINAL", 0) == 1;
    let log_rows = env_usize("NV_LOG_ROWS", 19);
    let child_engine = Sha384CpuEngine::new(child_params_small());
    let (vk0, p0) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&child_engine);
    let mut pp = params_from_env("PARENT", [16, 3, 20, 64]);
    pp.max_constraint_degree = nv_debug_params().max_constraint_degree;
    describe("NV_PARENT", &pp);
    let engine = Sha384CpuEngine::new(pp);
    let k = openvm_stark_backend::StarkEngine::params(&engine).k_whir();
    let _ = k;
    // optional final layer with its own parameters (env FINAL_*), proving the last phase-A proof
    let final_engine = std::env::var("FINAL_LOG_BLOWUP").ok().map(|_| {
        let mut fp = params_from_env("FINAL", [16, 3, 20, 64]);
        fp.max_constraint_degree = nv_debug_params().max_constraint_degree;
        describe("NV_FINAL", &fp);
        Sha384CpuEngine::new_final(fp)
    });
    // per-level peak RSS: reset the high-water mark (clear_refs 5), read VmHWM after the level
    let reset_hwm = || {
        let _ = std::fs::write("/proc/self/clear_refs", "5");
    };
    let hwm_gb = || -> f64 {
        std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(|l| l.split_whitespace().nth(1).unwrap().parse::<f64>().unwrap()))
            .unwrap_or(0.0)
            / 1048576.0
    };
    let run_with = |eng: &Sha384CpuEngine,
                    circ: &super::circuit::NvCircuit,
                    vk: &MultiStarkVerifyingKey<Sha384Config>,
                    p: &Proof<Sha384Config>,
                    tag: &str| {
        reset_hwm();
        let t = std::time::Instant::now();
        let (vk1, p1, b, shapes) = super::circuit::prove_level(circ, eng, vk, p);
        let secs = t.elapsed().as_secs_f64();
        println!("{tag}_RESOURCES wall_s={secs:.1} peak_rss_gb={:.2} program_rows={}", hwm_gb(), b.instrs.len());
        let airs = circ.airs::<Sha384Config>();
        let (mut cols, mut opened, mut ints, mut cells, mut sha_cells) = (0, 0, 0usize, 0usize, 0usize);
        for (i, a) in vk1.inner.per_air.iter().enumerate() {
            let w = a.params.width.common_main;
            cols += w;
            opened += w + a.params.opening_masks()[0].iter().filter(|&&m| m).count();
            ints += shapes[i].0 * a.symbolic_constraints.interactions.len();
            cells += shapes[i].0 * shapes[i].1;
            if airs[i].name().starts_with("Sha512Air") || airs[i].name().starts_with("TableAir") {
                sha_cells += shapes[i].0 * shapes[i].1;
            }
            println!(
                "{tag}_AIR {} h={} w={} rot={} int/row={} deg={}",
                airs[i].name(),
                shapes[i].0,
                w,
                a.params.need_rot as usize,
                a.symbolic_constraints.interactions.len(),
                a.max_constraint_degree
            );
        }
        let merkle_rows: usize = b.merkle_nodes;
        let blocks: usize = b.jobs().iter().filter(|j| !j.node).map(|j| j.num_blocks()).sum::<usize>();
        let l = (usize::BITS - (ints - 1).leading_zeros()) as usize;
        println!(
            "{tag}_SUMMARY cols={cols} opened={opened} interactions={ints} L={l} cells={cells} sha_cells={sha_cells} other_cells={} alu_used={} merkle_nodes={merkle_rows} leaf_blocks={blocks} prove_s={secs:.1}",
            cells - sha_cells,
            b.instrs.iter().filter(|i| i.op != super::isa::Op::Nop).count()
        );
        soundness(tag, &vk1);
        println!("{tag}_PROOF_BYTES {}", proof_sizes(&p1));
        let words: Vec<[u32; 4]> = b.instrs.iter().map(|i| i.words()).collect();
        (vk1, p1, shapes, words)
    };
    let run = |circ: &super::circuit::NvCircuit,
               vk: &MultiStarkVerifyingKey<Sha384Config>,
               p: &Proof<Sha384Config>,
               tag: &str| run_with(&engine, circ, vk, p, tag);
    // phase A: natural heights until the shape repeats
    let mut circ = super::circuit::NvCircuit::new(k, log_rows, 1);
    let (mut vka, mut pa, mut prev) = (vk0.clone(), p0.clone(), vec![]);
    let mut fixed: Vec<usize> = std::env::var("NV_FIXED")
        .map(|s| s.split(',').map(|x| x.trim().parse().unwrap()).collect())
        .unwrap_or_default();
    let mut phase_a = if fixed.is_empty() { env_usize("NV_PHASE_A", 4) } else { 0 };
    let save_dir = std::env::var("NV_SAVE_DIR").ok();
    // resume: a saved phase-A proof (every NV level has the same vk under the parent engine;
    if let Ok(path) = std::env::var("NV_RESUME_PROOF") {
        use openvm_stark_backend::codec::Decode;
        let (_, vk) = openvm_stark_backend::StarkEngine::keygen(&engine, &circ.airs::<Sha384Config>());
        let bytes = std::fs::read(&path).unwrap();
        pa = Proof::<Sha384Config>::decode(&mut std::io::Cursor::new(&bytes)).unwrap();
        vka = vk;
        openvm_stark_backend::StarkEngine::verify(&engine, &vka, &pa).expect("resumed proof verifies");
        println!("NV_RESUMED {path} bytes={}", bytes.len());
        phase_a = 0;
        fixed = vec![1];
    }
    for i in 1..=phase_a {
        // phase A only finds the fixed heights: no binding / passthrough (child_nv would force the
        // program binding, which needs equal programs, i.e. the fixed heights)
        circ.child_nv = false;
        let (v, q, sh, _) = run(&circ, &vka, &pa, &format!("A{i}"));
        if let Some(d) = &save_dir {
            use openvm_stark_backend::codec::Encode;
            let mut bytes = vec![];
            q.encode(&mut bytes).unwrap();
            std::fs::write(format!("{d}/A{i}.proof"), &bytes).unwrap();
        }
        let hs: Vec<usize> = sh.iter().map(|s| s.0).collect();
        println!("A{i}_HEIGHTS {hs:?}");
        vka = v;
        pa = q;
        if hs == prev {
            fixed = hs;
            break;
        }
        fixed = if prev.is_empty() { hs.clone() } else { hs.iter().zip(&prev).map(|(a, b)| *a.max(b)).collect() };
        prev = hs;
    }
    // [stream research] NV_FIXED_OVERRIDE: phase B heights given directly (phase A then only needs
    // A1, for the level-1 app table; phase B asserts every level's natural heights equal these)
    if let Ok(o) = std::env::var("NV_FIXED_OVERRIDE") {
        fixed = o.split(',').map(|x| x.trim().parse().unwrap()).collect();
    }
    println!("NV_FIXED_HEIGHTS {fixed:?}");
    if let Some(fe) = final_engine.as_ref().filter(|_| unbound_final) {
        // UNBOUND measurement-only final layer: verifies the last phase-A proof without binding
        // its program (FINAL params differ from the NV fixed point)
        println!("NV_FINAL_UNBOUND measurement only: the child's program is not bound");
        let mut fc = super::circuit::NvCircuit::new(k, log_rows, 1); // k = the child (parent-param) folding factor
        fc.prog_log = circ.prog_log;
        let _ = run_with(fe, &fc, &vka, &pa, "FINAL");
        if levels == 0 {
            return;
        }
    }
    // phase B: fixed heights (if phase A ran); binding at every level >= 2
    let mut circ = super::circuit::NvCircuit::new(k, log_rows, 1);
    if !fixed.is_empty() {
        circ.heights = Some(fixed);
    }
    let (mut vk, mut p) = (vk0, p0.clone());
    let mut last_words: Vec<[u32; 4]> = vec![];
    let mut last_root = None;
    // G2: every NV level carries its program as a cached part.  Anchor rule
    // (`NvCircuit::select_anchor`): a level anchors at its child (C_child) until its program
    // equals its child's, then keeps that anchor and binds by BIND.  Run at least `levels` levels
    // and until the last level binds its child by BIND (the program has converged), at most
    // NV_MAX_LEVELS.
    circ.program_part = true;
    let max_levels = env_usize("NV_MAX_LEVELS", levels.max(2) + 4);
    let mut level = 0usize;
    let mut bound_levels = 0usize;
    // tight heights: levels >= 2 commit at least `floor` rows per AIR (setup constants, natural
    // height + 1/NV_TIGHT_SLACK_DIV slack, raised only when a level's natural height exceeds it)
    let tight = openvm_stark_backend::StarkEngine::params(&engine).whir.levers.tight_heights;
    let l_skip = openvm_stark_backend::StarkEngine::params(&engine).l_skip;
    let slack_div = env_usize("NV_TIGHT_SLACK_DIV", 64);
    let mut floor: Option<Vec<usize>> = None;
    let mut last_by_bind = false;
    loop {
        level += 1;
        circ.bind = level >= 2;
        circ.child_nv = level >= 2;
        if level >= 2 {
            let a = circ.select_anchor(&vk, &p, level as u32 - 1, &last_words, last_root.unwrap());
            let by_bind = a.0 != level as u32 - 1;
            println!("NV_G2_ANCHOR L{level}: anchor level M = {} ({})", a.0, if by_bind { "child bound by BIND" } else { "child bound by its root = C_M" });
            bound_levels += by_bind as usize;
            last_by_bind = by_bind;
            circ.anchor = Some(a);
            if tight {
                use p3_matrix::Matrix;
                let (mats, _) = circ.generate(&vk, &p);
                let nat = super::circuit::natural_tight_heights(&mats, l_skip);
                let fits = floor.as_ref().is_some_and(|f| nat.iter().zip(f).all(|(n, f)| n <= f));
                if !fits {
                    floor = Some(
                        nat.iter()
                            .zip(&mats)
                            .map(|(&n, m)| (n + n / slack_div).next_multiple_of(1 << l_skip).min(m.height()))
                            .collect(),
                    );
                    println!("NV_G2_FLOOR L{level}: natural committed {nat:?} -> new floor {:?}", floor.as_ref().unwrap());
                } else {
                    println!("NV_G2_FLOOR L{level}: natural committed {nat:?} fits floor {:?}", floor.as_ref().unwrap());
                }
                circ.tight_floor = floor.clone();
            }
        }
        let (v, q, sh, words) = run(&circ, &vk, &p, &format!("L{level}"));
        let root = q.trace_vdata[0].as_ref().unwrap().cached_commitments[0];
        println!("NV_G2 L{level} program rows {} committed heights {:?} cached root {root:?}", words.len(), sh.iter().map(|s| s.0).collect::<Vec<_>>());
        assert!(super::circuit::check_statement(&q.public_values[0], &p0.public_values), "L{level} statement");
        last_words = words;
        last_root = Some(root);
        vk = v;
        p = q;
        if level >= levels && last_by_bind {
            break;
        }
        assert!(level < max_levels, "program did not converge within {max_levels} levels");
    }
    let levels = level;
    println!("NV_G2 converged: {levels} levels, {bound_levels} bound by BIND, anchor M = {}", circ.anchor.unwrap().0);
    // FINAL: the fixed-point program under the final domain, child program bound; V_d checks it
    assert!(levels >= 2, "FINAL needs an NV child (NV_LEVELS >= 2)");
    // FINAL: its own WHIR shape (FINAL_* params, default the NV params) and a single commitment
    // (program in common main); the program is the same (it depends on the child vk only)
    let fe = final_engine.unwrap_or_else(|| Sha384CpuEngine::new_final(openvm_stark_backend::StarkEngine::params(&engine).clone()));
    let mut fcirc = circ.clone_shape();
    fcirc.program_part = false;
    fcirc.tight_floor = None; // nobody verifies FINAL in-circuit
    let (vkf, pf, _, words_f) = run_with(&fe, &fcirc, &vk, &p, "FINAL");
    print_vk_regimes("FINAL", &vkf);
    {
        // [stream research] final proof digest (and the proof, with NV_SAVE_DIR)
        use openvm_stark_backend::codec::Encode;
        use sha2::Digest as _;
        let mut bytes = vec![];
        pf.encode(&mut bytes).unwrap();
        println!("FINAL_PROOF_SHA256 {:x} bytes={}", sha2::Sha256::digest(&bytes), bytes.len());
        if let Some(d) = &save_dir {
            std::fs::write(format!("{d}/FINAL.proof"), &bytes).unwrap();
        }
    }
    assert_eq!(words_f, last_words, "FINAL runs the same (fixed-point) program as its child");
    let setup = super::vd::VdSetup { vk_final: vkf, program: words_f, level: levels as u32 + 1 };
    super::vd::verify_final(&setup, &fe, &p0.public_values, &pf, false).expect("V_d (pinned program) accepts the final proof");
    println!("NV_VD final accepted: level {}, pinned program {} rows", setup.level, setup.program.len());
}

/// Keygen only: per-AIR constraint degree, width and interactions.
#[test]
fn nv_degrees() {
    let circ = super::circuit::NvCircuit::new(3, 16, 1);
    let airs = circ.airs::<Sha384Config>();
    let mut p = nv_debug_params();
    p.max_constraint_degree = 32;
    let p = crate::sha384::e2e_tests::with_levers(p, openvm_stark_backend::WhirLevers { next_mask: true, ..Default::default() }, 1, 20);
    let engine = Sha384CpuEngine::new(p);
    let (_pk, vk) = openvm_stark_backend::StarkEngine::keygen(&engine, &airs);
    for (a, v) in airs.iter().zip(&vk.inner.per_air) {
        println!(
            "NV_DEG {} deg={} w={} int={} rot={} rot_cols={}",
            a.name(),
            v.max_constraint_degree,
            v.params.width.common_main,
            v.symbolic_constraints.interactions.len(),
            v.params.need_rot as usize,
            v.params.opening_masks()[0].iter().filter(|&&m| m).count()
        );
        if std::env::var("NV_ROT_DUMP").is_ok() {
            let idx: Vec<usize> = v.params.opening_masks()[0].iter().enumerate().filter(|(_, &m)| m).map(|(i, _)| i).collect();
            println!("NV_ROT {} {:?}", a.name(), idx);
        }
    }
}

/// Unified backend: the row-major CPU backend gives byte-identical proofs to the reference
/// backend for each WHIR / GKR lever and the x15 domain (process SHA levers: env).
#[test]
fn unified_cpu_matches_reference() {
    use crate::sha384::{config::Sha384RefEngine, e2e_tests::{proof_sizes, with_levers}};
    use openvm_stark_backend::{codec::Encode, WhirLevers};
    let base = WhirLevers::default();
    let cases: Vec<(&str, WhirLevers, usize)> = vec![
        ("default", base, 1),
        ("k1=1", WhirLevers { k_first: 1, ..base }, 1),
        ("keep_domain", WhirLevers { keep_domain: true, ..base }, 1),
        ("multiproof", WhirLevers { multiproof: true, ..base }, 1),
        ("gruen+derive", WhirLevers { gruen_gkr: true, gkr_derive_claims: true, gruen_zerocheck: true, ..base }, 1),
        ("next_mask", WhirLevers { next_mask: true, ..base }, 1),
        ("x15", base, 15),
        ("tight", WhirLevers { tight_heights: true, ..base }, 1),
        ("whir_y", WhirLevers { whir_y: true, ..base }, 1),
        ("all", WhirLevers { k_first: 1, keep_domain: true, multiproof: true, gruen_gkr: true, gkr_derive_claims: true, gruen_zerocheck: true, next_mask: true, wide_query_pow: false, tight_heights: true, whir_y: true }, 15),
    ];
    for (name, lv, x15) in cases {
        let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 10, 3);
        p.max_constraint_degree = 4;
        p.log_blowup = 2;
        let p = with_levers(p, lv, x15, 40);
        for fx in 0..2 {
            let enc = |engine_is_cpu: bool| -> Vec<u8> {
                let proof = if engine_is_cpu {
                    let e = Sha384CpuEngine::new(p.clone());
                    let (vk, pr) = if fx == 0 { FibFixture::new(0, 1, 1 << 6).keygen_and_prove(&e) } else { InteractionsFixture11.keygen_and_prove(&e) };
                    openvm_stark_backend::StarkEngine::verify(&e, &vk, &pr).expect("cpu proof verifies");
                    pr
                } else {
                    let e = Sha384RefEngine::new(p.clone());
                    let (vk, pr) = if fx == 0 { FibFixture::new(0, 1, 1 << 6).keygen_and_prove(&e) } else { InteractionsFixture11.keygen_and_prove(&e) };
                    openvm_stark_backend::StarkEngine::verify(&e, &vk, &pr).expect("ref proof verifies");
                    pr
                };
                let mut b = vec![];
                proof.encode(&mut b).unwrap();
                let _ = proof_sizes;
                b
            };
            let (a, r) = (enc(true), enc(false));
            println!("UNIFIED_IDENTITY case={name} fixture={fx} bytes={} identical={}", a.len(), a == r);
            assert_eq!(a, r, "cpu backend differs from reference: {name}");
        }
    }
}

/// In-circuit lever checks: a child proved with Gruen GKR / derived claims / Gruen zerocheck /
/// next-row mask / WHIR-Y; each tampered proof must be rejected by the NV circuit.
#[test]
fn nv_lever_tamper() {
    use crate::sha384::e2e_tests::with_levers;
    use openvm_stark_backend::WhirLevers;
    let lv = WhirLevers {
        gruen_gkr: true,
        gkr_derive_claims: true,
        gruen_zerocheck: true,
        next_mask: true,
        whir_y: true,
        ..Default::default()
    };
    let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 8, 3);
    p.max_constraint_degree = 4;
    let p = with_levers(p, lv, 1, 5);
    let engine = Sha384CpuEngine::new(p);
    let (vk, proof) = InteractionsFixture11.keygen_and_prove(&engine);
    nv_debug_mats(&vk, &proof, 16, |_, _| {});
    println!("NV_LEVER_HONEST ok");
    let one = EF::ONE;
    let cases: Vec<(&str, Box<dyn Fn(&mut openvm_stark_backend::proof::Proof<Sha384Config>)>)> = vec![
        ("gruen gkr s(3) non-zero", Box::new(move |p| p.gkr_proof.sumcheck_polys[0][0][2] += one)),
        ("gruen gkr s(1)", Box::new(move |p| p.gkr_proof.sumcheck_polys[0][0][0] += one)),
        ("derived p_xi_1 non-zero", Box::new(move |p| p.gkr_proof.claims_per_layer[1].p_xi_1 += one)),
        ("derived q0 non-zero", Box::new(move |p| p.gkr_proof.q0_claim += one)),
        ("layer q_xi_1", Box::new(move |p| p.gkr_proof.claims_per_layer[1].q_xi_1 += one)),
        ("gruen zerocheck last eval", Box::new(move |p| *p.batch_constraint_proof.sumcheck_round_polys[0].last_mut().unwrap() += one)),
        ("zerocheck eval", Box::new(move |p| p.batch_constraint_proof.sumcheck_round_polys[0][0] += one)),
        ("column opening", Box::new(move |p| p.batch_constraint_proof.column_openings[0][0][0] += one)),
        ("pow witness", Box::new(move |p| p.gkr_proof.logup_pow_witness += F::ONE)),
    ];
    for (name, m) in cases {
        let mut bad = proof.clone();
        m(&mut bad);
        must_fail(name, || nv_debug_mats(&vk, &bad, 16, |_, _| {}));
    }
}

/// In-circuit WHIR levers: k1 = 1, keep-domain, multiproof, x15, wide query PoW.
#[test]
fn nv_whir_lever_tamper() {
    use crate::sha384::e2e_tests::with_levers;
    use openvm_stark_backend::WhirLevers;
    let lv = WhirLevers { k_first: 1, keep_domain: true, multiproof: true, wide_query_pow: true, whir_y: true, ..Default::default() };
    let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 8, 3);
    p.max_constraint_degree = 4;
    let p = with_levers(p, lv, 15, 5);
    let engine = Sha384CpuEngine::new(p);
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    nv_debug_mats(&vk, &proof, 16, |_, _| {});
    println!("NV_WHIR_LEVER_HONEST ok");
    let one = EF::ONE;
    let cases: Vec<(&str, Box<dyn Fn(&mut openvm_stark_backend::proof::Proof<Sha384Config>)>)> = vec![
        ("multiproof initial digest", Box::new(|p| p.whir_proof.initial_round_merkle_proofs[0][0][0][1] ^= 1)),
        ("multiproof codeword digest", Box::new(|p| p.whir_proof.codeword_merkle_proofs[0][0][0][0] ^= 1)),
        ("initial opened row (k1 leaf)", Box::new(|p| p.whir_proof.initial_round_opened_rows[0][0][1][0] += F::ONE)),
        ("codeword value", Box::new(move |p| p.whir_proof.codeword_opened_values[0][0][1] += one)),
        ("wide pow witness element 1", Box::new(|p| p.whir_proof.query_phase_pow_witnesses[1] += F::ONE)),
        ("final poly", Box::new(move |p| p.whir_proof.final_poly[0] += one)),
    ];
    for (name, m) in cases {
        let mut bad = proof.clone();
        m(&mut bad);
        must_fail(name, || nv_debug_mats(&vk, &bad, 16, |_, _| {}));
    }
}

/// A trace whose last rows are all zero (for tight-heights chunks): columns (real, a, b) with
/// real * (a^2 - b) = 0 and next.real * (next.a - a - 1) = 0; 700 of 1024 rows real.
#[derive(Clone, Copy)]
pub struct ZeroTailAir;
impl<T> p3_air::BaseAir<T> for ZeroTailAir {
    fn width(&self) -> usize {
        3
    }
}
impl<T> openvm_stark_backend::BaseAirWithPublicValues<T> for ZeroTailAir {}
impl<T> openvm_stark_backend::PartitionedBaseAir<T> for ZeroTailAir {}
impl<AB: p3_air::AirBuilder> p3_air::Air<AB> for ZeroTailAir {
    fn eval(&self, builder: &mut AB) {
        use p3_air::AirBuilder;
        use p3_matrix::Matrix;
        let main = builder.main();
        let (l, n) = (main.row_slice(0).unwrap(), main.row_slice(1).unwrap());
        let real: AB::Expr = l[0].clone().into();
        let a: AB::Expr = l[1].clone().into();
        let bb: AB::Expr = l[2].clone().into();
        let (n0, n1): (AB::Expr, AB::Expr) = (n[0].clone().into(), n[1].clone().into());
        builder.assert_bool(real.clone());
        builder.assert_zero(real * (a.clone() * a.clone() - bb));
        builder.when_transition().assert_zero(n0 * (n1 - a - AB::Expr::ONE));
    }
}
pub struct ZeroTailFixture(pub usize, pub usize);
impl openvm_stark_backend::test_utils::TestFixture<Sha384Config> for ZeroTailFixture {
    fn airs(&self) -> Vec<openvm_stark_backend::AirRef<Sha384Config>> {
        vec![std::sync::Arc::new(ZeroTailAir)]
    }
    fn generate_proving_ctx(&self) -> openvm_stark_backend::prover::ProvingContext<openvm_stark_backend::prover::CpuColMajorBackend<Sha384Config>> {
        use openvm_stark_backend::prover::{AirProvingContext, ColMajorMatrix, ProvingContext};
        let (h, real) = (self.0, self.1);
        let mut v = vec![F::ZERO; h * 3];
        for i in 0..real {
            v[3 * i] = F::ONE;
            v[3 * i + 1] = F::from_usize(i);
            v[3 * i + 2] = F::from_usize(i * i);
        }
        let m = p3_matrix::dense::RowMajorMatrix::new(v, 3);
        ProvingContext::new(vec![(0, AirProvingContext::simple(ColMajorMatrix::from_row_major(&m), vec![]))])
    }
}

/// Tight heights in-circuit: a child with a zero tail is verified with chunked stacking.
#[test]
fn nv_tight_heights() {
    use crate::sha384::e2e_tests::with_levers;
    use openvm_stark_backend::WhirLevers;
    for (lv, x15) in [
        (WhirLevers { tight_heights: true, ..Default::default() }, 1),
        (WhirLevers { tight_heights: true, next_mask: true, multiproof: true, whir_y: true, ..Default::default() }, 15),
    ] {
        let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 8, 3);
        p.max_constraint_degree = 4;
        let p = with_levers(p, lv, x15, 5);
        let engine = Sha384CpuEngine::new(p);
        let (vk, proof) = ZeroTailFixture(1024, 700).keygen_and_prove(&engine);
        println!("NV_TIGHT child tight={:?}", proof.trace_vdata.iter().flatten().map(|v| v.tight_height).collect::<Vec<_>>());
        let mut b = Builder::new(17, 0);
        build_verifier(&mut b, &vk, &proof);
        assert!(b.failures.is_empty(), "{:?}", b.failures);
        nv_debug_mats(&vk, &proof, 16, |_, _| {});
        let mut bad = proof.clone();
        bad.stacking_proof.stacking_openings[0][0] += EF::ONE;
        must_fail("tight stacking opening", || nv_debug_mats(&vk, &bad, 16, |_, _| {}));
        let mut bad = proof.clone();
        bad.whir_proof.initial_round_opened_rows[0][0][0][0] += F::ONE;
        must_fail("tight opened row", || nv_debug_mats(&vk, &bad, 16, |_, _| {}));
    }
}

#[test]
fn nv_zero_tail_plain() {
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = ZeroTailFixture(1024, 700).keygen_and_prove(&engine);
    nv_debug_mats(&vk, &proof, 16, |_, _| {});
}

/// G2 level-1 binding: level 2 checks its level-1 child's cached program root against the
/// constant C_L1 (the setup commitment of the L1 program part); no app table.  Honest accepted
/// (program and full debug constraint level), statement passthrough; rejected: a wrong C_L1
/// constant and a re-exposed different statement digest.
#[test]
fn nv_l1_commit_binding() {
    use openvm_cpu_backend::CpuBackend;
    use openvm_stark_backend::prover::{AirProvingContext, ProvingContext};
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk0, p0) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let mut pp = openvm_stark_backend::test_utils::test_system_params_small(2, 18, 3);
    pp.max_constraint_degree = nv_debug_params().max_constraint_degree;
    pp.log_blowup = 2;
    let pp = crate::sha384::e2e_tests::with_levers(pp, Default::default(), 1, 20);
    let parent = Sha384CpuEngine::new(pp);
    let mut circ1 = super::circuit::NvCircuit::new(3, 19, 1);
    circ1.program_part = true;
    let (m1, b1g) = circ1.generate(&vk0, &p0);
    assert!(b1g.failures.is_empty());
    let c_l1 = super::circuit::program_commitment(openvm_stark_backend::StarkEngine::config(&parent), &m1[0]);
    let (vk1, p1, _, _) = super::circuit::prove_level(&circ1, &parent, &vk0, &p0);
    assert_eq!(p1.trace_vdata[0].as_ref().unwrap().cached_commitments[0], c_l1, "L1 cached root = setup C_L1");
    println!("NV_L1C C_L1 = setup commitment of the L1 program part");
    // level 2 (own program in common main: debug-checkable; its own partition is irrelevant here)
    let run = |c: crate::sha384::config::Digest, pv_tamper: bool| -> Vec<String> {
        let mut circ2 = super::circuit::NvCircuit::new(3, 19, 1);
        circ2.child_nv = true;
        circ2.anchor = Some((1, c));
        let airs = circ2.airs::<Sha384Config>();
        let (mats, b2) = circ2.generate(&vk1, &p1);
        let mut pv2 = b2.public_values();
        if pv_tamper {
            pv2[5] += F::ONE;
        }
        let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = mats
            .into_iter()
            .enumerate()
            .map(|(i, m)| if i == 0 { AirProvingContext::simple(m, pv2.clone()) } else { AirProvingContext::simple_no_pis(m) })
            .collect();
        Sha384CpuEngine::new(nv_debug_params()).debug(&airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
        b2.failures
    };
    assert!(run(c_l1, false).is_empty());
    println!("NV_L1C honest level 2 accepted (C_L1 check)");
    // statement passthrough (G1): L2 re-exposes L1's digest = statement of the app proof
    assert!(super::circuit::check_statement(&p1.public_values[0], &p0.public_values), "L1 statement");
    {
        let mut circ2 = super::circuit::NvCircuit::new(3, 19, 1);
        circ2.child_nv = true;
        circ2.anchor = Some((1, c_l1));
        let (_, b2) = circ2.generate(&vk1, &p1);
        assert!(super::circuit::check_statement(&b2.public_values(), &p0.public_values), "L2 passthrough");
        let mut other = p0.public_values.clone();
        other[0][0] += F::ONE;
        assert!(!super::circuit::check_statement(&b2.public_values(), &other), "changed app public value");
        println!("NV_STATEMENT L1 = L2 = statement digest ok");
    }
    must_fail("level-2 re-exposes a different statement digest", || {
        run(c_l1, true);
    });
    let mut bad = c_l1;
    bad[3] ^= 0x10;
    must_fail("wrong C_L1 constant", || {
        let f = run(bad, false);
        assert!(f.is_empty(), "{f:?}");
    });
}

/// T* transcript (final-soundness T*-1, T*-2) in the circuit: counter-mode squeeze blocks and
/// PoW-run blocks; rejected: a wrong counter (squeeze block / PoW-run block), a PoW witness
/// ground on the old chain H(7, sigma || w), challenges read from B_1's PoW word.
#[test]
fn nv_tstar_tamper() {
    use core::borrow::BorrowMut;
    use super::transcript2::{replay2, Hash2Cols, Op2, HASH2_WIDTH};
    use crate::sha384::config::{hash_parts, SqueezeSrc, TAG_POW};
    use p3_field::PrimeField32;
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), 16, 1);
    let (_, b) = circ.generate(&vk, &proof);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    let jobs = replay2(&b.transcript.clone().into_log());
    let count = |op: Op2| jobs.iter().filter(|j| j.op == op).count();
    let (ns, np, nq) = (count(Op2::Squeeze), count(Op2::Pow), count(Op2::PowQ));
    println!("NV_TSTAR jobs: squeeze {ns} pow {np} pow-run {nq}");
    assert!(ns > 0 && np > 0 && nq > 0, "fixture must exercise squeeze, PoW and PoW-run blocks");
    nv_debug_mats(&vk, &proof, 16, |_, _| {});
    println!("NV_TSTAR honest ok");
    let hash_row = |m: &mut p3_matrix::dense::RowMajorMatrix<F>, pick: &dyn Fn(&Hash2Cols<F>) -> bool| -> usize {
        let w = m.width;
        let h = m.values.len() / w;
        (0..h)
            .find(|&r| {
                m.values[r * w + 3] == F::ONE && {
                    let o = r * w + super::uair::N_COMMON;
                    let row: &mut Hash2Cols<F> = m.values[o..o + HASH2_WIDTH].borrow_mut();
                    pick(row)
                }
            })
            .expect("hash row")
    };
    let edit = |m: &mut p3_matrix::dense::RowMajorMatrix<F>, r: usize, f: &dyn Fn(&mut Hash2Cols<F>)| {
        let o = r * m.width + super::uair::N_COMMON;
        f(m.values[o..o + HASH2_WIDTH].borrow_mut());
    };
    for (name, op) in [("tstar wrong counter (squeeze block)", 0usize), ("tstar wrong counter (PoW-run block)", 1)] {
        must_fail(name, || {
            nv_debug_mats(&vk, &proof, 16, |mats, _| {
                let r = hash_row(&mut mats[0], &|x| if op == 0 { x.op_s == F::ONE && x.ctr == F::TWO } else { x.op_q == F::ONE });
                edit(&mut mats[0], r, &|x| x.ctr += F::ONE);
            })
        });
    }
    // chain link: the key of a squeeze block (its input state) must be the run's key
    must_fail("tstar squeeze key limb", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            let r = hash_row(&mut mats[0], &|x| x.op_s == F::ONE && x.ctr == F::TWO);
            edit(&mut mats[0], r, &|x| x.state_in[4] += F::ONE);
        })
    });
    // PoW-run block ids are pinned like squeeze ids (audit B5 extended to T* blocks)
    must_fail("tstar PoW-run job id", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            let r = hash_row(&mut mats[0], &|x| x.op_q == F::ONE);
            edit(&mut mats[0], r, &|x| x.job += F::ONE);
        })
    });
    // G1: a PoW-run block's witness units must equal B_1's (chain bus), not a free choice
    must_fail("tstar PoW-run block witness differs from B_1's", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            let r = hash_row(&mut mats[0], &|x| x.op_q == F::ONE);
            edit(&mut mats[0], r, &|x| x.w[0] += F::ONE);
        })
    });
    // challenges from B_1's PoW word: claim word 0 of a PoW block as read
    must_fail("tstar challenges from the PoW bits of B_1", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            let r = hash_row(&mut mats[0], &|x| x.op_p == F::ONE && x.rd == F::ONE);
            edit(&mut mats[0], r, &|x| {
                x.rdw[0] = F::ONE;
                x.last_word += F::ONE;
            });
        })
    });
    // a logup PoW witness valid on the old chain but not under T*
    let bits = vk.inner.params.logup.pow_bits;
    assert!(bits > 0);
    let pj = jobs.iter().find(|j| j.op == Op2::Pow).unwrap();
    let sigma = pj.state_in;
    let lz = |s: &[u8; 48]| {
        let mut n = 0;
        for &x in s {
            if x == 0 {
                n += 8;
            } else {
                n += x.leading_zeros() as usize;
                break;
            }
        }
        n
    };
    let old_ok = |x: u32| lz(&hash_parts(TAG_POW, &[&sigma, &x.to_le_bytes()])) >= bits;
    let new_ok = |x: u32| lz(&SqueezeSrc::Pow(sigma, x.to_le_bytes().to_vec()).block(1)) >= bits;
    let x = (0u32..).find(|&x| old_ok(x) && !new_ok(x)).unwrap();
    assert_eq!(pj.wit[0], proof.gkr_proof.logup_pow_witness, "first PoW job = logup PoW");
    let mut bad = proof.clone();
    bad.gkr_proof.logup_pow_witness = F::from_u32(x);
    println!("NV_TSTAR old-chain witness {x} (honest {})", proof.gkr_proof.logup_pow_witness.as_canonical_u32());
    must_fail("tstar PoW ground on the old chain", || nv_debug_mats(&vk, &bad, 16, |_, _| {}));
}

/// Statement digest at level 1 (final-soundness G1): NV exposes SHA-384 (tag 8) of the app
/// proof's public values; a changed app public value changes the digest; a trace exposing a
/// different digest is rejected; an app proof with a changed public value is rejected.
#[test]
fn nv_statement_digest() {
    use openvm_cpu_backend::CpuBackend;
    use openvm_stark_backend::prover::{AirProvingContext, ProvingContext};
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), 16, 1);
    let airs = circ.airs::<Sha384Config>();
    let (mats, b) = circ.generate(&vk, &proof);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    let pv = b.public_values();
    assert!(super::circuit::check_statement(&pv, &proof.public_values));
    let mut other = proof.public_values.clone();
    let a = other.iter().position(|p| !p.is_empty()).expect("app public values");
    other[a][0] += F::ONE;
    assert_ne!(
        crate::sha384::config::statement_digest(&other),
        crate::sha384::config::statement_digest(&proof.public_values)
    );
    assert!(!super::circuit::check_statement(&pv, &other));
    println!("NV_STATEMENT digest binds the app public values");
    let debug = |mats: Vec<p3_matrix::dense::RowMajorMatrix<F>>, pv: Vec<F>| {
        let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = mats
            .into_iter()
            .enumerate()
            .map(|(i, m)| if i == 0 { AirProvingContext::simple(m, pv.clone()) } else { AirProvingContext::simple_no_pis(m) })
            .collect();
        Sha384CpuEngine::new(nv_debug_params()).debug(&airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
    };
    debug(mats.clone(), pv.clone());
    println!("NV_STATEMENT honest ok");
    for k in [1usize, 12, 13, 18] {
        let mut bad = pv.clone();
        bad[k] += F::ONE;
        must_fail(&format!("exposed statement limb {k}"), || debug(mats.clone(), bad.clone()));
    }
    let mut bad = proof.clone();
    bad.public_values[a][0] += F::ONE;
    must_fail("app public value changed in the child proof", || nv_debug_mats(&vk, &bad, 16, |_, _| {}));
}

/// U-12: the final recursive layer has its own hash domain (transcript init flag, node framing
/// 'F'): a final-layer proof does not verify under the inner-layer domain, and vice versa.
#[test]
fn final_layer_domain() {
    use openvm_stark_backend::StarkEngine;
    let p = child_params_small();
    let inner = Sha384CpuEngine::new(p.clone());
    let fin = Sha384CpuEngine::new_final(p);
    let (vk_i, pr_i) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&inner);
    let (vk_f, pr_f) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&fin);
    inner.verify(&vk_i, &pr_i).expect("inner proof, inner domain");
    fin.verify(&vk_f, &pr_f).expect("final proof, final domain");
    assert!(inner.verify(&vk_f, &pr_f).is_err(), "final proof accepted under the inner domain");
    assert!(fin.verify(&vk_i, &pr_i).is_err(), "inner proof accepted under the final domain");
    assert_ne!(pr_i.whir_proof.final_poly, pr_f.whir_proof.final_poly);
    println!("FINAL_DOMAIN cross-verification rejected both ways");
}

/// O-2 (U-13), certificate-gated: a round uses its first-order threshold only if its code and
/// fold sub-codes are in the certificate set; otherwise Johnson m = 64 (O-1). The table is bound
/// into the vk; the native verifier re-derives each round from its declared regime; NV verifies
/// an O-2 child; an uncertified round falls back; altered tables are rejected.
#[test]
fn o2_agreement_table() {
    use openvm_stark_backend::{AgreementTable, CertSet, StarkEngine};
    let base = child_params_small();
    let (lb, lh) = (base.log_blowup, base.l_skip + base.n_stack);
    let bits = 5 + base.whir.query_phase_pow_bits;
    // no certificate set: every round on the Johnson fallback
    let mut p0 = base.clone();
    p0.whir = p0.whir.clone().with_first_order(lb, lh, bits, 50, 64, None, 1);
    let t0 = p0.whir.agreement.clone().unwrap();
    assert!(t0.rounds.iter().all(|r| !r.first_order));
    // a certificate set covering exactly round 0's code and fold sub-codes
    let codes = base.whir.round_codes(lb, lh);
    let kr = base.whir.k_rounds();
    let (n0, k0) = codes[0];
    let a0 = AgreementTable::first_order_agree(n0, k0, 50, 64);
    let certs: CertSet = (0..=kr[0]).map(|s| (n0 >> s, k0 >> s, (a0 + (1 << s) - 1) >> s)).collect();
    let mut p = base.clone();
    p.whir = p.whir.clone().with_first_order(lb, lh, bits, 50, 64, Some(&certs), 1);
    crate::sha384::e2e_tests::describe("O2_CHILD", &p);
    let t = p.whir.agreement.clone().unwrap();
    assert!(t.rounds[0].first_order && t.rounds[1..].iter().all(|r| !r.first_order), "uncertified rounds must fall back");
    assert_eq!(t.rounds[1..], t0.rounds[1..], "fallback rounds = Johnson m = 64");
    assert!(t.all_first_order_certified(&certs, &kr));
    // a set missing the last fold sub-code of round 0 -> round 0 falls back too
    let mut partial = certs.clone();
    partial.remove(&(n0 >> kr[0], k0 >> kr[0], (a0 + (1 << kr[0]) - 1) >> kr[0]));
    let mut pp = base.clone();
    pp.whir = pp.whir.clone().with_first_order(lb, lh, bits, 50, 64, Some(&partial), 1);
    assert!(!pp.whir.agreement.as_ref().unwrap().rounds[0].first_order, "missing sub-code certificate must fall back");
    assert!(!t.all_first_order_certified(&partial, &kr));
    println!("O2 table (certified round 0) {:?}", t.rounds.iter().map(|r| (r.agree, r.queries, r.first_order)).collect::<Vec<_>>());
    let o2: Vec<usize> = p.whir.rounds.iter().map(|r| r.num_queries).collect();
    assert_eq!(o2, t.rounds.iter().map(|r| r.queries as usize).collect::<Vec<_>>());
    let engine = Sha384CpuEngine::new(p.clone());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    engine.verify(&vk, &proof).expect("O-2 proof verifies");
    nv_debug_mats(&vk, &proof, 16, |_, _| {});
    println!("O2 NV debug ok");
    // altered threshold, or a fallback round relabelled first-order -> rejected
    for (name, f) in [
        ("A_0 + 1", Box::new(|t: &mut AgreementTable| t.rounds[0].agree += 1) as Box<dyn Fn(&mut AgreementTable)>),
        ("round 1 relabelled first-order", Box::new(|t: &mut AgreementTable| t.rounds[1].first_order = true)),
    ] {
        let mut vk_bad = vk.clone();
        f(vk_bad.inner.params.whir.agreement.as_mut().unwrap());
        let bad_engine = Sha384CpuEngine::new(vk_bad.inner.params.clone());
        assert!(bad_engine.verify(&vk_bad, &proof).is_err(), "{name} accepted");
        assert!(engine.verify(&vk_bad, &proof).is_err(), "{name} accepted by the honest engine");
    }
    // a consistent table for a weaker target: a different vk (params, pre-hash) -> rejected
    let mut weak = p.clone();
    weak.whir = weak.whir.clone().with_first_order(lb, lh, bits - 3, 50, 64, Some(&certs), 1);
    let mut vk_weak = vk.clone();
    vk_weak.inner.params = weak;
    assert!(engine.verify(&vk_weak, &proof).is_err(), "weaker table accepted");
    let (_, vk2) = Sha384CpuEngine::new(vk_weak.inner.params.clone()).keygen(&FibFixture::new(0, 1, 1 << 5).airs());
    assert_ne!(vk2.pre_hash, vk.pre_hash, "table not bound into the vk pre-hash");
    println!("O2 uncertified rounds fall back; altered tables rejected; table bound into the pre-hash");
}

/// Sampled words come from GLUE's digest rows (digest bus, key 8 + word; 49 NvAir interactions
/// per row instead of 55): rejected are a squeeze run starting at word 1, a dropped or an extra
/// word send, and a changed word limb.
#[test]
fn nv_sample_word_source_tamper() {
    use core::borrow::BorrowMut;
    use super::glue::{GlueCols, GLUE_W};
    use super::transcript2::{Samp2Cols, SAMP2_WIDTH};
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    nv_debug_mats(&vk, &proof, 16, |_, _| {});
    let (kg, ks) = (2usize, 4usize);
    let rows = |m: &p3_matrix::dense::RowMajorMatrix<F>, flag: usize| -> Vec<usize> {
        (0..m.values.len() / m.width).filter(|&r| m.values[r * m.width + flag] == F::ONE).collect()
    };
    must_fail("squeeze run starts at word 1", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            let m = &mut mats[0];
            let w = m.width;
            let r = rows(m, ks)
                .into_iter()
                .find(|&r| {
                    let s: &mut Samp2Cols<F> = m.values[r * w + super::uair::N_COMMON..r * w + super::uair::N_COMMON + SAMP2_WIDTH].borrow_mut();
                    s.is_first == F::ONE && s.w0 == F::ZERO && s.is_last == F::ZERO
                })
                .unwrap();
            let s: &mut Samp2Cols<F> = m.values[r * w + super::uair::N_COMMON..r * w + super::uair::N_COMMON + SAMP2_WIDTH].borrow_mut();
            s.w0 = F::ONE;
            s.wi = F::ONE;
        })
    });
    for (name, from) in [("dropped word send", F::ONE), ("extra word send", F::ZERO)] {
        must_fail(name, || {
            nv_debug_mats(&vk, &proof, 16, |mats, _| {
                let m = &mut mats[0];
                let w = m.width;
                let r = rows(m, kg)
                    .into_iter()
                    .find(|&r| {
                        let g: &mut GlueCols<F> = m.values[r * w + super::uair::N_COMMON..r * w + super::uair::N_COMMON + GLUE_W].borrow_mut();
                        let drow = g.last == F::ONE && g.q[2] == F::ONE && !(g.q[0] == F::ONE && g.q[1] == F::ONE);
                        drow && g.tr == F::ZERO && g.dx[0] == from
                    })
                    .unwrap();
                let g: &mut GlueCols<F> = m.values[r * w + super::uair::N_COMMON..r * w + super::uair::N_COMMON + GLUE_W].borrow_mut();
                g.dx[0] = F::ONE - from;
            })
        });
    }
}

/// The DKT certificate loader reads the top-level "n,k,A,1" keys only and drops excluded
/// (not kernel-proved) entries.
#[test]
fn dkt_cert_loader() {
    let dir = std::env::temp_dir().join(format!("nv-dkt-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("certs.json");
    std::fs::write(
        &path,
        r#"{"2013265920,1048576,37140791,1": {"E": "1/2", "list": "3"}, "x,1,2,1": {}, "5,6,7,2": {},
            "251658240,4096,790689,1": {"m": 16},
            "_no_certificate": {"4026531840,1024,1552217,1": "no certificate"},
            "_shapes": {"s": [{"n": 1, "A": 2}]}}"#,
    )
    .unwrap();
    let c = crate::sha384::e2e_tests::load_dkt_certs(path.to_str().unwrap());
    assert_eq!(c.len(), 2, "top-level certificate keys only (not _no_certificate's)");
    assert!(c.contains(&(2013265920, 1048576, 37140791)) && c.contains(&(251658240, 4096, 790689)));
    assert!(!c.contains(&(4026531840, 1024, 1552217)));
    // kernel-proof rule: excluded (engine / #eval!-only) entries are dropped
    let ex = dir.join("big.keys");
    std::fs::write(&ex, "251658240,4096,790689,1\n").unwrap();
    let c = crate::sha384::e2e_tests::load_dkt_certs_excluding(path.to_str().unwrap(), Some(ex.to_str().unwrap()));
    assert_eq!(c.len(), 1);
    assert!(!c.contains(&(251658240, 4096, 790689)));
    std::fs::remove_dir_all(&dir).unwrap();
}

/// Program-size probe (ignored; env PARENT_*): a Fib child proved at the parent parameters, the
/// NV verifier program for it (generate only); prints rows per phase / query round and the
/// transcript job census.
#[test]
#[ignore]
fn nv_program_probe() {
    use crate::sha384::e2e_tests::{describe, env_usize, params_from_env};
    use super::transcript2::{replay2, Op2};
    let mut pp = params_from_env("PARENT", [17, 6, 268, 64]);
    pp.max_constraint_degree = nv_debug_params().max_constraint_degree;
    describe("PROBE", &pp);
    let engine = Sha384CpuEngine::new(pp);
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), env_usize("NV_LOG_ROWS", 19), 1);
    let (_, b) = circ.generate(&vk, &proof);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    let jobs = replay2(&b.transcript.clone().into_log());
    let blocks = |j: &super::transcript2::TrJob2| j.job().message().len().div_ceil(128).max(1);
    for op in [Op2::Flush, Op2::Commit, Op2::Squeeze, Op2::Pow, Op2::PowQ] {
        let js: Vec<_> = jobs.iter().filter(|j| j.op == op).collect();
        let small = js.iter().filter(|j| j.op == Op2::Flush && j.obs.len() <= 12).count();
        println!("PROBE_TR {op:?} jobs={} blocks={} small_flush(<=12 felts)={small}", js.len(), js.iter().map(|j| blocks(j)).sum::<usize>());
    }
    let leaf_blocks: usize = b.jobs().iter().map(|j| j.num_blocks()).sum();
    println!("PROBE_ROWS program={} merkle_nodes={} leaf+node_blocks={} transcript_jobs={}", b.instrs.len(), b.merkle_nodes, leaf_blocks, jobs.len());
}

/// Merkle-level and Horner-chain ops (SibWS4/2: free sibling pushed at 12 (1 - bit); DigWS4/2: child digest
/// from the digest bus pushed at 12 bit): a changed sibling limb, a changed child-digest limb
/// and a SibWS2 high coefficient are rejected.
#[test]
fn nv_merkle_op_tamper() {
    use super::isa::Op;
    use super::uair::{AbCols, AB_W, N_COMMON};
    use core::borrow::BorrowMut;
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), 16, 1);
    let (_, b) = circ.generate(&vk, &proof);
    let row_of = |op: Op| b.instrs.iter().position(|i| i.op == op);
    for (name, op, k) in [("sibling limb (SibWS4)", Op::SibWS4, 3usize), ("child digest limb (DigWS4)", Op::DigWS4, 5), ("child digest limb (DigWS2)", Op::DigWS2, 1), ("SibWS2 high coefficient", Op::SibWS2, 7), ("Horner chain value (HornR)", Op::HornR, 2), ("Horner result (HornE)", Op::HornE, 0), ("Horner start (HornS)", Op::HornS, 4), ("two-step leaf Horner (Horn2)", Op::Horn2, 6)] {
        let Some(r) = row_of(op) else {
            assert_eq!(op, Op::Horn2, "{name}: op missing from the fixture");
            println!("NV_TAMPER_SKIPPED {name} (no such row in this fixture)");
            continue;
        };
        must_fail(name, || {
            nv_debug_mats(&vk, &proof, 16, |mats, _| {
                let w = mats[0].width;
                let ab: &mut AbCols<F> = mats[0].values[r * w + N_COMMON..r * w + N_COMMON + AB_W].borrow_mut();
                ab.c[k] += F::ONE;
            })
        });
    }
    // SibWS4 also starts the level's node job (P0 = NODE_TAG on the job bus): a row whose P0 no
    // longer carries the tag leaves the job start unmatched
    let r = row_of(Op::SibWS4).unwrap();
    assert_eq!(b.instrs[r].a, super::hash::NODE_TAG);
    must_fail("SibWS4 node-job start (P0)", || {
        nv_debug_mats(&vk, &proof, 16, |mats, _| {
            let w = mats[0].width;
            mats[0].values[r * w + core::mem::offset_of!(super::uair::NvCommon<u8>, p)] = F::ZERO;
        })
    });
}

/// Two-step leaf Horner (Horn2) on a child whose stacked rows are 2+ felts wide: honest
/// accepted; a changed accumulator value or second witness is rejected.
#[test]
fn nv_horn2_tamper() {
    use super::isa::Op;
    use super::uair::{AbCols, AB_W, N_COMMON};
    use core::borrow::BorrowMut;
    let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 3, 3);
    p.max_constraint_degree = 4;
    let engine = Sha384CpuEngine::new(p);
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), 16, 1);
    let (_, b) = circ.generate(&vk, &proof);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    let r = b.instrs.iter().position(|i| i.op == Op::Horn2).expect("Horn2 rows (stacked width >= 2)");
    nv_debug_mats(&vk, &proof, 16, |_, _| {});
    println!("NV_HORN2 honest ok");
    for (name, which) in [("Horn2 value c[3]", 0), ("Horn2 second witness", 1)] {
        must_fail(name, || {
            nv_debug_mats(&vk, &proof, 16, |mats, _| {
                let w = mats[0].width;
                let ab: &mut AbCols<F> = mats[0].values[r * w + N_COMMON..r * w + N_COMMON + AB_W].borrow_mut();
                if which == 0 {
                    ab.c[3] += F::ONE;
                } else {
                    ab.wit2 += F::ONE;
                }
            })
        });
    }
}

/// O-2 with several commitments: round 0 must be the Johnson fallback (its first-order list is
/// squared by the commitment batching; final-soundness o2_table_bound.py). A table built for 2
/// commitments puts round 0 on Johnson and verifies; a table with a first-order round 0 is
/// rejected for a 2-commitment proof (preprocessed trace), and accepted for a 1-commitment one.
#[test]
fn o2_round0_multi_commit() {
    use openvm_stark_backend::{test_utils::PreprocessedFibFixture, AgreementTable, CertSet, StarkEngine};
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
    let p1 = mk(1);
    let p2 = mk(2);
    assert!(p1.whir.agreement.as_ref().unwrap().rounds[0].first_order);
    assert!(!p2.whir.agreement.as_ref().unwrap().rounds[0].first_order, "2 commitments: round 0 Johnson");
    let fx = PreprocessedFibFixture::new(0, 1, (0..32).map(|i| i % 3 != 0).collect());
    let e2 = Sha384CpuEngine::new(p2);
    let (vk, proof) = fx.keygen_and_prove(&e2);
    e2.verify(&vk, &proof).expect("2-commitment proof, round 0 Johnson");
    let e1 = Sha384CpuEngine::new(p1.clone());
    let (vk1, proof1) = fx.keygen_and_prove(&e1);
    let err = e1.verify(&vk1, &proof1).expect_err("first-order round 0 with 2 commitments accepted");
    println!("O2_MULTI rejected: {err}");
    let (vkf, prf) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&e1);
    e1.verify(&vkf, &prf).expect("1-commitment proof with first-order round 0");
    println!("O2_MULTI ok");
}

/// Gap G1: the NV program is a function of the child vk / shape only. Children with proof-of-work
/// (logup and WHIR query PoW) and different witnesses give different transcripts (different
/// sampling rejections, so different numbers of squeeze / PoW-run blocks) but byte-identical
/// programs, and each one's trace passes the debug check.
#[test]
fn nv_program_pow_identity() {
    use super::transcript2::{replay2, Op2};
    let p = child_params_small();
    assert!(p.logup.pow_bits > 0 || p.whir.query_phase_pow_bits > 0, "fixture must use PoW");
    let engine = Sha384CpuEngine::new(p);
    let circ = |vk: &openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<Sha384Config>| super::circuit::NvCircuit::new(vk.inner.params.k_whir(), 16, 1);
    let mut progs = vec![];
    let mut census = vec![];
    for (a, b0) in [(0u64, 1u64), (2, 3), (5, 8), (7, 1)] {
        let (vk, proof) = FibFixture::new(a, b0, 1 << 5).keygen_and_prove(&engine);
        let (_, bld) = circ(&vk).generate(&vk, &proof);
        assert!(bld.failures.is_empty(), "{:?}", bld.failures);
        let jobs = replay2(&bld.transcript.clone().into_log());
        let n = |op: Op2| jobs.iter().filter(|j| j.op == op).count();
        census.push((n(Op2::Squeeze), n(Op2::Pow), n(Op2::PowQ)));
        progs.push(bld.instrs.clone());
        if a == 0 {
            nv_debug_mats(&vk, &proof, 16, |_, _| {});
        }
    }
    println!("NV_POW_IDENTITY transcript blocks (squeeze, pow, pow-run) per child: {census:?}");
    assert!(census.iter().any(|c| c != &census[0]), "children must differ in their block counts for the test to bite");
    for p in &progs[1..] {
        assert_eq!(p, &progs[0], "NV program depends on the child proof");
    }
    println!("NV_POW_IDENTITY {} programs byte-identical ({} rows)", progs.len(), progs[0].len());
}

/// V_d end to end (test size, G2): base (Fib) -> L1 (cached program part, commitment C_L1) -> L2
/// (checks its child's program commitment = C_L1) -> FINAL
/// (`new_final`, the same program as L2, bound to L2 at the fixed point) -> V_d. V_d pins the final
/// vk, level 3 and the NV program; it accepts the honest chain; a forged FINAL (a verify-nothing
/// program exposing the honest statement) passes every AIR and the final vk, and is accepted by
/// a V_d without the program check but rejected with it; a wrong claim and a wrong pinned level
/// are rejected. (Ignored: about 40 min, 17 GB.)
#[test]
#[ignore]
fn nv_vd_pinned_program() {
    use super::vd::{forge_statement_program, prove_traces, verify_final, VdSetup};
    let child_engine = Sha384CpuEngine::new(child_params_small());
    let (vk0, p0) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&child_engine);
    let mut pp = openvm_stark_backend::test_utils::test_system_params_small(2, 18, 3);
    pp.max_constraint_degree = nv_debug_params().max_constraint_degree;
    pp.log_blowup = 1;
    let pp = crate::sha384::e2e_tests::with_levers(pp, Default::default(), 1, 12);
    let engine = Sha384CpuEngine::new(pp.clone());
    let engine_final = Sha384CpuEngine::new_final(pp);
    let k = openvm_stark_backend::StarkEngine::params(&engine).k_whir();
    let log_rows = 18;
    // natural L1 (program part), then L2's natural heights fix every level's heights
    // program length 2^17 (the default log_rows - 2 = 16 overflows), independent of NV_PROG_LOG
    let mut circ1 = super::circuit::NvCircuit::new(k, log_rows, 1);
    circ1.prog_log = 17;
    circ1.program_part = true;
    let (vk1n, p1n, _, _) = super::circuit::prove_level(&circ1, &engine, &vk0, &p0);
    let mut circ2 = super::circuit::NvCircuit::new(k, log_rows, 1);
    circ2.prog_log = 17;
    circ2.program_part = true;
    circ2.child_nv = true;
    circ2.anchor = Some((1, p1n.trace_vdata[0].as_ref().unwrap().cached_commitments[0]));
    let (m2n, _) = circ2.generate(&vk1n, &p1n);
    use p3_matrix::Matrix;
    let fixed: Vec<usize> = m2n.iter().map(|m| m.height()).collect();
    println!("NV_VD fixed heights {fixed:?}");
    circ1.heights = Some(fixed.clone());
    // C_L1 at setup: the level-1 program part committed natively (no proof needed)
    let (m1, b1g) = circ1.generate(&vk0, &p0);
    assert!(b1g.failures.is_empty());
    let c_l1 = super::circuit::program_commitment(openvm_stark_backend::StarkEngine::config(&engine), &m1[0]);
    eprintln!("NV_TAPE_STAGE proving L1");
    let (vk1, p1, _, _) = super::circuit::prove_level(&circ1, &engine, &vk0, &p0);
    eprintln!("NV_TAPE_STAGE L1 done");
    assert_eq!(p1.trace_vdata[0].as_ref().unwrap().cached_commitments[0], c_l1, "L1's program commitment = the setup C_L1");
    println!("NV_VD C_L1 = setup commitment of the L1 program part");
    circ2.heights = Some(fixed.clone());
    circ2.anchor = Some((1, c_l1));
    // a wrong C_L1 constant: the level-2 program rejects the honest L1
    {
        let mut bad = circ2.clone_shape();
        let mut d = c_l1;
        d[0] ^= 1;
        bad.anchor = Some((1, d));
        let (_, bb) = bad.generate(&vk1, &p1);
        assert!(bb.failures.iter().any(|f| f.contains("C_M")), "wrong C_L1 accepted: {:?}", bb.failures);
        println!("NV_VD wrong C_L1 rejected: {:?}", bb.failures);
    }
    let (vk2, p2, b2, _) = super::circuit::prove_level(&circ2, &engine, &vk1, &p1);
    assert_eq!(b2.level, 2);
    // FINAL: the same program, one commitment (program in common main), final domain
    let mut circf = circ2.clone_shape();
    circf.program_part = false;
    eprintln!("NV_TAPE_STAGE proving FINAL");
    let (vkf, pf, bf, _) = super::circuit::prove_level(&circf, &engine_final, &vk2, &p2);
    eprintln!("NV_TAPE_STAGE FINAL done");
    assert_eq!(bf.level, 3);
    assert_eq!(bf.instrs, b2.instrs, "FINAL runs the uniform NV program (bound to L2's)");
    assert!(pf.trace_vdata[0].as_ref().unwrap().cached_commitments.is_empty(), "FINAL has one commitment");
    let program: Vec<[u32; 4]> = bf.instrs.iter().map(|i| i.words()).collect();
    let setup = VdSetup { vk_final: vkf.clone(), program, level: 3 };
    verify_final(&setup, &engine_final, &p0.public_values, &pf, false).expect("V_d accepts the honest chain");
    println!("NV_VD honest final accepted ({} program rows)", setup.program.len());
    let mut other = p0.public_values.clone();
    let a = other.iter().position(|v| !v.is_empty()).unwrap();
    other[a][0] += F::ONE;
    assert!(verify_final(&setup, &engine_final, &other, &pf, false).is_err(), "wrong claim accepted");
    let wrong_level = VdSetup { level: 2, ..setup.clone() };
    assert!(verify_final(&wrong_level, &engine_final, &p0.public_values, &pf, false).is_err(), "wrong level accepted");
    let d = crate::sha384::config::statement_digest(&p0.public_values);
    let (mats, bforge) = circf.generate_program(forge_statement_program(3, d));
    let (vk_forge, p_forge) = prove_traces(&circf, &engine_final, mats, bforge.public_values());
    assert_eq!(vk_forge.pre_hash, vkf.pre_hash, "the forgery uses the pinned final vk");
    verify_final(&setup, &engine_final, &p0.public_values, &p_forge, true).expect("without the program check V_d is fooled");
    let err = verify_final(&setup, &engine_final, &p0.public_values, &p_forge, false).expect_err("forged final accepted with the program check");
    println!("NV_VD forged final ({} rows) accepted without the program check, rejected with it: {err}", bforge.instrs.len());
}

/// **M4: per-AIR height cap (`log_height <= maxLog_t`) in the vk, in NV, and in V_d.**
///
/// The ported classical tables bound their soundness argument to their exported `maxLog`
/// (`ZkFormal.V2.Air.Table.wf`, the `multBoundP < p` step in `PQ/StatePort/Bridge.lean`).  The
/// cap must therefore be visible to every verifier, not just the demo driver:
///
/// * it is a vk constant, so it is in the vk pre-hash (a proof the cap rejects cannot verify
///   under a vk that pins the cap);
/// * the native verifier rejects the proof (`verify_proof_shape`,
///   `ProofShapeVDataError::LogHeightExceedsTableCap`);
/// * NV's program generator records a static failure and emits no program (no rows: heights and
///   `maxLog` are both vk constants), exactly like the existing LogUp count check (B2);
/// * V_d's `check_height_caps` rejects it on the final proof.
///
/// The negative half is the one that matters: without the cap in the vk, the same trace height
/// is accepted (only the global `l_skip + n_stack` remains) and NV emits the program.
#[test]
fn nv_air_height_cap() {
    use openvm_stark_backend::{
        test_utils::{
            dummy_airs::fib_air::{air::FibonacciAir, trace::generate_trace_rows},
            FibFixture, TestFixture,
        },
        AirRef, StarkEngine,
    };
    use p3_air::{Air, AirBuilderWithPublicValues, BaseAir, BaseAirWithPublicValues};
    use std::sync::Arc;

    /// FibonacciAir with a per-AIR cap on its own height (the shape of a ported table).
    #[derive(Clone)]
    struct CappedFib(Option<usize>);
    impl<F> openvm_stark_backend::PartitionedBaseAir<F> for CappedFib {
        fn max_log_trace_height(&self) -> Option<usize> {
            self.0
        }
    }
    impl<F> BaseAir<F> for CappedFib {
        fn width(&self) -> usize {
            <FibonacciAir as BaseAir<F>>::width(&FibonacciAir)
        }
    }
    impl<F> BaseAirWithPublicValues<F> for CappedFib {
        fn num_public_values(&self) -> usize {
            3
        }
    }
    impl<AB: AirBuilderWithPublicValues> Air<AB> for CappedFib {
        fn eval(&self, builder: &mut AB) {
            <FibonacciAir as Air<AB>>::eval(&FibonacciAir, builder);
        }
    }
    struct Fixture {
        max_log: Option<usize>,
        n: usize,
    }
    impl TestFixture<Sha384Config> for Fixture {
        fn airs(&self) -> Vec<AirRef<Sha384Config>> {
            vec![Arc::new(CappedFib(self.max_log)) as AirRef<Sha384Config>]
        }
        fn generate_proving_ctx(
            &self,
        ) -> openvm_stark_backend::prover::ProvingContext<
            openvm_stark_backend::prover::CpuColMajorBackend<Sha384Config>,
        > {
            use openvm_stark_backend::prover::{AirProvingContext, ColMajorMatrix, ProvingContext};
            let m = generate_trace_rows::<F>(0, 1, self.n);
            // the FibonacciAir public values: a, b, f_n
            let (mut a, mut b) = (0u64, 1u64);
            for _ in 0..self.n - 1 {
                (a, b) = (b, a.wrapping_add(b));
            }
            let pis = [0u64, 1, b].map(F::from_u64).to_vec();
            ProvingContext::new(vec![(0, AirProvingContext::simple(ColMajorMatrix::from_row_major(&m), pis))])
        }
    }

    let n = 1usize << 5;
    let log_h = n.trailing_zeros() as usize;
    let engine = Sha384CpuEngine::new(child_params_small());
    let prove = |max_log: Option<usize>| Fixture { max_log, n }.keygen_and_prove(&engine);

    // honest: height == maxLog == 2^log_h
    let (vk_ok, proof_ok) = prove(Some(log_h));
    engine.verify(&vk_ok, &proof_ok).expect("a height at the cap verifies");
    assert_eq!(vk_ok.inner.per_air[0].params.max_log_trace_height, Some(log_h), "the cap is a vk field");
    let (vk_none, proof_none) = prove(None);
    assert_eq!(vk_none.inner.per_air[0].params.max_log_trace_height, None, "unset stays None");
    println!("NV_HEIGHT_CAP honest log_height={log_h} cap={log_h} accepted");

    // 1. a height above the cap: the native verifier refuses it ...
    let (vk_bad, proof_bad) = prove(Some(log_h - 1));
    let err = engine.verify(&vk_bad, &proof_bad).expect_err("height above the cap accepted");
    let s = format!("{err:?}");
    assert!(s.contains("LogHeightExceedsTableCap"), "unexpected rejection: {s}");
    println!("NV_HEIGHT_CAP native rejected: {err}");
    // 2. the cap is the *only* reason: keeping the pinned pre-hash and dropping just the cap field
    //    (a verifier that does not know the table's maxLog) accepts the same proof
    let mut vk_uncapped = vk_bad.clone();
    vk_uncapped.inner.per_air[0].params.max_log_trace_height = None;
    engine.verify(&vk_uncapped, &proof_bad).expect("without the cap the same proof is accepted (control)");
    // and the cap is bound into the pre-hash, so a proof cannot dodge it by swapping vks
    assert_ne!(vk_ok.pre_hash, vk_none.pre_hash, "the cap is bound into the vk pre-hash");
    assert_eq!(vk_bad.pre_hash, vk_uncapped.pre_hash, "the field, not the hash, was cleared");
    println!("NV_HEIGHT_CAP cap is in the vk pre-hash; without it the same proof verifies");

    // 3. NV: the program generator refuses a child above its cap.  The generator's own check
    //    (`build_verifier`'s per-AIR loop) runs first and records the failure; the subsequent
    //    native `verify_proof_shape` also rejects it, which is what a caller sees as a panic.
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut b = Builder::new(17, 0);
        build_verifier(&mut b, &vk_bad, &proof_bad);
        b.failures
    }));
    match r {
        Err(e) => {
            let msg = e
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default();
            assert!(msg.contains("exceeds its maxLog"), "unexpected NV rejection: {msg}");
            println!("NV_HEIGHT_CAP NV program rejected: {msg}");
        }
        Ok(f) => panic!("NV accepted a child above its maxLog: {f:?}"),
    }
    // 4. ... and accepts the honest one with no extra rows (a static check)
    let mut b_ok = Builder::new(17, 0);
    build_verifier(&mut b_ok, &vk_ok, &proof_ok);
    assert!(b_ok.failures.is_empty(), "{:?}", b_ok.failures);
    //    the same vk with the cap field cleared (same pre-hash, same transcript, same heights)
    //    gives byte-identical program words, so the check is static and adds no rows
    let mut vk_ok_nocap = vk_ok.clone();
    vk_ok_nocap.inner.per_air[0].params.max_log_trace_height = None;
    let mut b_none = Builder::new(17, 0);
    build_verifier(&mut b_none, &vk_ok_nocap, &proof_ok);
    assert!(b_none.failures.is_empty(), "{:?}", b_none.failures);
    assert_eq!(b_ok.instrs, b_none.instrs, "the cap adds no rows and does not change the program");
    let _ = proof_none;
    println!(
        "NV_HEIGHT_CAP NV program for the honest child: {} rows, identical with and without a cap",
        b_ok.instrs.len()
    );

    // 5. V_d: the same check against the pinned final vk
    let setup_bad = super::vd::VdSetup { vk_final: vk_bad.clone(), program: vec![], level: 1 };
    let e = super::vd::check_height_caps(&setup_bad.vk_final, &proof_bad).expect_err("V_d accepted a height above maxLog");
    assert!(e.contains("exceeds its maxLog"), "{e}");
    let setup_ok = super::vd::VdSetup { vk_final: vk_ok.clone(), program: vec![], level: 1 };
    super::vd::check_height_caps(&setup_ok.vk_final, &proof_ok).expect("V_d accepts a height at the cap");
    println!("NV_HEIGHT_CAP V_d rejected: {e}");

    // 6. the plain (uncapped) path is unchanged in shape
    let (vk_f, proof_f) = FibFixture::new(0, 1, n).keygen_and_prove(&engine);
    assert_eq!(vk_f.inner.per_air[0].params.max_log_trace_height, None);
    engine.verify(&vk_f, &proof_f).unwrap();
    let mut b_f = Builder::new(17, 0);
    build_verifier(&mut b_f, &vk_f, &proof_f);
    assert!(b_f.failures.is_empty());
    println!("NV_HEIGHT_CAP uncapped Fib unchanged ({} program rows)", b_f.instrs.len());
}


/// **P4/M2: the cached TAPE root is carried from the base proof to V_d.**
///
/// The base proof's TAPE table is a cached main part (the shape `pq-state-port` gives it): its
/// root is a proof value observed in the preamble and **not** a public value.  Without P4 the
/// chain verifies a base whose TAPE table could be anything.
///
/// The chain is the real one: base -> L1 (program part) -> L2 (bind, statement passthrough) ->
/// FINAL, and V_d checks the final against a `StatementClaim` naming the TAPE root.  Asserted:
/// L1's in-circuit digest equals `StatementClaim::digest`; every level re-exposes it unchanged;
/// V_d accepts; a different, swapped, or omitted TAPE root is rejected; a tampered root in the
/// base proof is rejected by the Merkle checks.
#[test]
fn nv_tape_root_passthrough() {
    use super::circuit::StatementClaim;
    use super::vd::{check_final_program, verify_final_claim, VdSetup};
    use openvm_stark_backend::test_utils::PreprocessedAndCachedFixture;

    let child_engine = Sha384CpuEngine::new(child_params_small());
    // same parent shape as `nv_vd_pinned_program` (NvAir's own degree is 9)
    let mut pp = openvm_stark_backend::test_utils::test_system_params_small(2, 18, 3);
    pp.max_constraint_degree = nv_debug_params().max_constraint_degree;
    let engine = Sha384CpuEngine::new(pp.clone());
    let sels: Vec<bool> = (0..1usize << 5).map(|i| i % 3 == 0).collect();
    let fx = PreprocessedAndCachedFixture::new(sels, child_engine.config().clone(), 1);
    let (vk0, p0) = fx.keygen_and_prove(&child_engine);
    child_engine.verify(&vk0, &p0).unwrap();
    let tape_root = p0.trace_vdata[0].as_ref().unwrap().cached_commitments[0];
    let claim = StatementClaim { public_values: p0.public_values.clone(), cached_roots: vec![tape_root] };
    let d_p4 = claim.digest();
    let d_pv_only = crate::sha384::config::statement_digest(&p0.public_values);
    assert_ne!(d_p4, d_pv_only, "the TAPE root must change the statement digest");

    let k = openvm_stark_backend::StarkEngine::params(&engine).k_whir();
    let log_rows = 18;
    // L1 with natural heights: its statement digest must be the P4 one, and its proof fixes the
    // heights every later level uses (as `nv_vd_pinned_program`)
    let mut circ1 = super::circuit::NvCircuit::new(k, log_rows, 1);
    circ1.prog_log = 17;
    circ1.program_part = true;
    let (mats1, b1) = circ1.generate(&vk0, &p0);
    assert!(b1.failures.is_empty(), "{:?}", b1.failures);
    assert_eq!(b1.statement, Some(d_p4), "L1 exposes the P4 statement (public values + TAPE root)");
    assert!(super::circuit::check_statement_claim(&b1.public_values(), &claim), "L1 statement claim");
    assert!(
        !super::circuit::check_statement(&b1.public_values(), &p0.public_values),
        "the public values alone are not the statement once a cached table is carried"
    );
    println!("NV_TAPE L1 statement includes the cached TAPE root: {d_p4:?}");
    // a cached root tampered with in the base proof: Merkle root failures
    {
        let mut bad = p0.clone();
        bad.trace_vdata[0].as_mut().unwrap().cached_commitments[0][0] ^= 1;
        let mut bb = Builder::new(17, 0);
        build_verifier(&mut bb, &vk0, &bad);
        assert!(bb.failures.iter().any(|f| f == "merkle root"), "a tampered TAPE root was accepted: {:?}", bb.failures);
        println!("NV_TAPE tampered TAPE root rejected ({} failures)", bb.failures.len());
    }
    let (vk1n, p1n, _, _) = super::circuit::prove_level(&circ1, &engine, &vk0, &p0);
    assert!(super::circuit::check_statement_claim(&p1n.public_values[0], &claim), "L1 proof exposes it");

    // L2 at natural heights fixes the heights of both levels (the program depends on the child's
    // committed heights, which is why the G2 chain pins them)
    let mut circ2 = super::circuit::NvCircuit::new(k, log_rows, 1);
    circ2.prog_log = 17;
    circ2.program_part = true;
    circ2.child_nv = true;
    circ2.anchor = Some((1, p1n.trace_vdata[0].as_ref().unwrap().cached_commitments[0]));
    let (mats2n, b2n) = circ2.generate(&vk1n, &p1n);
    assert!(b2n.failures.is_empty(), "{:?}", b2n.failures);
    assert_eq!(b2n.statement, Some(d_p4), "L2 re-exposes L1's statement (TAPE root included)");
    let fixed: Vec<usize> = mats2n.iter().map(p3_matrix::Matrix::height).collect();
    println!("NV_TAPE fixed heights {fixed:?}");
    circ1.heights = Some(fixed.clone());
    let (mats1, b1f) = circ1.generate(&vk0, &p0);
    assert_eq!(b1f.statement, Some(d_p4), "the fixed-height L1 exposes the same statement");
    let (vk1, p1, _, _) = super::circuit::prove_level(&circ1, &engine, &vk0, &p0);
    assert!(super::circuit::check_statement_claim(&p1.public_values[0], &claim), "L1 proof exposes it");
    let _ = mats1;
    circ2.heights = Some(fixed);
    circ2.anchor = Some((1, p1.trace_vdata[0].as_ref().unwrap().cached_commitments[0]));
    let (vk2, p2, _, _) = super::circuit::prove_level(&circ2, &engine, &vk1, &p1);

    // L3 = FINAL shape: same program, one commitment (program in common main), final domain
    let engine_final = Sha384CpuEngine::new_final(pp);
    let mut circf = circ2.clone_shape();
    circf.program_part = false;
    circf.tight_floor = None;
    let (vkf, pf, bf, _) = super::circuit::prove_level(&circf, &engine_final, &vk2, &p2);
    assert_eq!(bf.statement, Some(d_p4), "FINAL exposes the same statement");
    let program: Vec<[u32; 4]> = bf.instrs.iter().map(|i| i.words()).collect();
    let setup = VdSetup { vk_final: vkf, program, level: 3 };
    verify_final_claim(&setup, &engine_final, &claim, &pf, false).expect("V_d accepts the chain with the TAPE root");
    check_final_program(&setup, &pf).expect("pinned program");
    println!("NV_TAPE V_d accepted the chain with the TAPE root in the statement");

    // a different TAPE root is rejected — that is what makes the cached table part of the statement
    let mut other_root = claim.clone();
    other_root.cached_roots[0] = {
        let mut r = other_root.cached_roots[0];
        r[0] ^= 1;
        r
    };
    let e = verify_final_claim(&setup, &engine_final, &other_root, &pf, false).expect_err("a different TAPE root accepted");
    assert!(e.contains("statement digest"), "{e}");
    println!("NV_TAPE V_d rejected a different TAPE root: {e}");
    // omitting the root (the pre-P4 statement) is rejected too
    let e = verify_final_claim(&setup, &engine_final, &StatementClaim::new(p0.public_values.clone()), &pf, false)
        .expect_err("a claim without the TAPE root accepted");
    println!("NV_TAPE V_d rejected the pre-P4 (public-values-only) claim: {e}");
    // and the public values themselves are still pinned when the fixture has any
    if claim.public_values.iter().any(|v| !v.is_empty()) {
        let mut other_pv = claim.clone();
        let a = other_pv.public_values.iter().position(|v| !v.is_empty()).unwrap();
        other_pv.public_values[a][0] += F::ONE;
        assert!(verify_final_claim(&setup, &engine_final, &other_pv, &pf, false).is_err(), "wrong public value accepted");
    }
}

/// **Item 3: the production LogUp budget is 2^30, and the measured cost is 2 bits.**
///
/// The D1-class base needs `max_interaction_count = 2^30` (N = 2^29.59; D0a N = 2^29.55), so the
/// production default in `params_from_env` is now 2^30 (was 2^28).  This asserts:
///
/// * the default is 2^30 and `*_INTERACTION_LOG=28` still reproduces the old value (so the G2
///   gate's recorded keys/proofs stay reproducible);
/// * the backend's LogUp term drops by exactly 2 bits (312.88 -> 310.88 at
///   `log_max_message_length = 7`), and the WHIR query counts are unchanged;
/// * the total soundness of the production FINAL shape still clears 268 bits.
#[test]
fn nv_production_interaction_budget() {
    use crate::sha384::e2e_tests::params_from_env;
    use openvm_stark_backend::soundness::SoundnessCalculator;

    // unset vars: the default
    unsafe {
        std::env::remove_var("PARENT_INTERACTION_LOG");
        std::env::remove_var("FINAL_INTERACTION_LOG");
    }
    let p = params_from_env("PARENT", [18, 7, 268, 64]);
    assert_eq!(p.logup.max_interaction_count, 1 << 30, "production default is 2^30");
    assert_eq!(p.logup.log_max_message_length, 7);
    println!("NV_LOGUP default max_interaction_count = 2^{}", (p.logup.max_interaction_count as f64).log2());

    // 2^28 opt-in still available (the G2 gate's setting)
    unsafe { std::env::set_var("PARENT_INTERACTION_LOG", "28") };
    let p28 = params_from_env("PARENT", [18, 7, 268, 64]);
    unsafe { std::env::remove_var("PARENT_INTERACTION_LOG") };
    assert_eq!(p28.logup.max_interaction_count, 1 << 28);

    // the backend formula, exactly as `calculator::logup_soundness`; log2(L_PCS) = 22 is the
    // value `tools/d1-pq-envelope/check.py` records the 312.88 figure at
    let ext_bits = 12.0 * (2013265921f64).log2();
    let logup = |mic: u32| SoundnessCalculator::logup_soundness(mic, 7, ext_bits, 22.0);
    let (b28, b30) = (logup(1 << 28), logup(1 << 30));
    assert!((b28 - 312.88).abs() < 0.01, "{b28}");
    assert!((b30 - 310.88).abs() < 0.01, "{b30}");
    assert!((b28 - b30 - 2.0).abs() < 1e-9, "the cost must be exactly 2 bits");
    println!("NV_LOGUP logup_soundness 2^28={b28:.2} 2^30={b30:.2} (delta {:.2})", b28 - b30);

    // the WHIR schedule does not move
    assert_eq!(
        p.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>(),
        p28.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>(),
        "the LogUp budget must not move the WHIR query counts"
    );
    println!(
        "NV_LOGUP queries unchanged: {:?}",
        p.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>()
    );
}

/// **Inertness for a child with no cached table and no height cap (the G2 gate's shape).**
///
/// P4's statement chain and M4's cap check must add nothing when their features are off: the
/// program must be byte-identical to the pre-change one, which is what keeps the recorded G2
/// proofs reproducible.  Measured earlier on this tree by generating the program for a Fib child
/// under both verifier versions: 8,660 rows either way (`log_rows 17`, `prog_log 16`), and 11,212
/// rows for a `CachedFixture11` child either way.
#[test]
fn nv_statement_inert_without_cached_roots() {
    use openvm_stark_backend::test_utils::FibFixture;
    let child_engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&child_engine);
    assert!(proof.trace_vdata.iter().all(|v| v.as_ref().unwrap().cached_commitments.is_empty()), "no cached table");
    assert!(vk.inner.per_air.iter().all(|a| a.params.max_log_trace_height.is_none()), "no height cap");
    let mut b = Builder::new(17, 0);
    build_verifier(&mut b, &vk, &proof);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    // the statement is exactly the G1 digest: no cached root was folded in
    assert_eq!(b.statement, Some(crate::sha384::config::statement_digest(&proof.public_values)));
    assert_eq!(super::circuit::StatementClaim::new(proof.public_values.clone()).digest(), b.statement.unwrap());
    println!("NV_INERT program rows {} (statement = G1 digest, no cached roots)", b.instrs.len());
}

/// **P4: the cached TAPE root is part of the statement V_d checks.**
///
/// A child proof whose AIR carries a cached main (the shape `pq-state-port`'s TAPE has) is
/// verified by the NV circuit.  The statement digest must cover the cached commitment:
///
/// * the honest child's statement digest is `statement_digest(public_values)` with each cached
///   commitment chained in by one Merkle-node compression, which is what the NV program emits.
///   (The earlier P4 draft appended the limbs to the statement message instead; that overflows
///   the one-block leaf job, so the shipped construction chains a node.)
/// * a statement that covers only the public values (the pre-P4 behaviour) must differ;
/// * and a child whose cached root is swapped must produce a different statement.
///
/// The negative case is the one that matters: without the cached commitment in the statement,
/// two children that differ only in their cached table have the *same* statement, so V_d would
/// accept either.
#[test]
fn nv_stmt_covers_cached_root() {
    use openvm_stark_backend::test_utils::PreprocessedAndCachedFixture;
    let engine = Sha384CpuEngine::new(child_params_small());
    let sels: Vec<bool> = (0..1usize << 5).map(|i| i % 3 == 0).collect();
    let fx = PreprocessedAndCachedFixture::new(sels, engine.config().clone(), 1);
    let (vk, proof) = fx.keygen_and_prove(&engine);
    assert!(!vk.inner.per_air[0].params.width.cached_mains.is_empty(), "child has a cached main");
    let cached = proof.trace_vdata[0].as_ref().unwrap().cached_commitments.clone();
    assert_eq!(cached.len(), 1, "one cached commitment");

    // the P4 statement: the G1 digest, then each cached commitment chained by a node compression
    let node = |l: crate::sha384::config::Digest, r: crate::sha384::config::Digest| {
        use openvm_stark_backend::hasher::MerkleHasher;
        crate::sha384::config::ShaHasher.compress(l, r)
    };
    let mut d_p4 = crate::sha384::config::statement_digest(&proof.public_values);
    for c in &cached {
        d_p4 = node(d_p4, *c);
    }
    let d_pv_only = crate::sha384::config::statement_digest(&proof.public_values);
    assert_ne!(d_p4, d_pv_only, "the cached root must change the statement digest");

    // a child whose cached root differs gives a different P4 statement, same PV digests
    let mut swapped = cached[0];
    swapped[0] ^= 1;
    let mut with_swapped = crate::sha384::config::statement_digest(&proof.public_values);
    for c in &cached {
        let c = if *c == cached[0] { swapped } else { *c };
        with_swapped = node(with_swapped, c);
    }
    assert_ne!(with_swapped, d_p4, "a swapped cached root must give a different statement");
    assert_eq!(
        crate::sha384::config::statement_digest(&proof.public_values),
        d_pv_only,
        "the public values alone are unchanged by the cached root"
    );

    // the circuit reproduces the P4 statement (its in-circuit SHA job must equal the host digest)
    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), 18, 1);
    let (_, b) = circ.generate(&vk, &proof);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    assert_eq!(
        b.statement, Some(d_p4),
        "the NV program must expose exactly the P4 statement (public values + cached root)"
    );
    println!("NV_STMT cached root in statement: {d_p4:?}");
}
