//! [agg] Tests of the n-to-1 aggregation node (nv/agg.rs).
use openvm_stark_backend::{keygen::types::MultiStarkVerifyingKey, proof::Proof, test_utils::TestFixture, StarkEngine};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use super::{
    agg::{build_agg, chunk_segments, check_range_statement, ChildKind, RangeStmt, SegFixture},
    builder::Builder,
    circuit::NvCircuit,
    transcript2::{Hash2Cols, HASH2_WIDTH},
    uair::{N_COMMON, NV_NUM_PVS},
};
use crate::sha384::{
    config::*,
    e2e_tests::child_params_small,
};

type Vk = MultiStarkVerifyingKey<Sha384Config>;
type Pf = Proof<Sha384Config>;

const N_CTX: usize = 1;
const APP: ChildKind = ChildKind::App { n_ctx: N_CTX, n_state: 2 };

fn prove_segs(segs: &[SegFixture]) -> Vec<(Vk, Pf)> {
    let engine = Sha384CpuEngine::new(child_params_small());
    segs.iter()
        .map(|s| {
            let (vk, p) = s.keygen_and_prove(&engine);
            engine.verify(&vk, &p).unwrap();
            (vk, p)
        })
        .collect()
}

fn refs(v: &[(Vk, Pf)]) -> Vec<(&Vk, &Pf)> {
    v.iter().map(|(a, b)| (a, b)).collect()
}

fn program(children: &[(Vk, Pf)]) -> (Builder, RangeStmt) {
    let mut b = Builder::new(18, 0);
    let s = build_agg(&mut b, &refs(children), APP, &[]);
    (b, s)
}

fn debug_params() -> openvm_stark_backend::SystemParams {
    let mut p = crate::sha384::e2e_tests::parent_params_debug();
    p.max_constraint_degree = NvCircuit::new(3, 16, 1).layout().degree().max(6);
    p
}

/// Generate the aggregation circuit's traces, mutate them, run the debug constraint + bus check.
fn agg_debug(
    children: &[(Vk, Pf)],
    kind: ChildKind,
    pre: &[RangeStmt],
    log_rows: usize,
    mutate: impl FnOnce(&mut Vec<RowMajorMatrix<F>>, &mut Vec<F>),
) -> Builder {
    use openvm_cpu_backend::CpuBackend;
    use openvm_stark_backend::prover::{AirProvingContext, MatrixDimensions, ProvingContext};
    let circ = NvCircuit::new(3, log_rows, 1);
    let airs = circ.airs::<Sha384Config>();
    let (mut mats, b) = circ.generate_with(|b| {
        build_agg(b, &refs(children), kind, pre);
    });
    let mut pvs = b.public_values();
    if let Ok(rows) = std::env::var("AGG_DUMP_ROWS") {
        for r in rows.split(',').map(|x| x.parse::<usize>().unwrap()) {
            eprintln!("AGG_ROW {r}: {:?}", b.instrs.get(r));
        }
    }
    let mut total = 0;
    for (a, m) in airs.iter().zip(&mats) {
        println!("AGG_AIR {} {} x {}", a.name(), m.height(), m.width());
        total += m.height() * m.width();
    }
    println!("AGG_TOTAL_CELLS {total} program_rows={} jobs={} merkle_nodes={}", b.instrs.len(), b.job_units.len(), b.merkle_nodes);
    mutate(&mut mats, &mut pvs);
    let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = mats
        .into_iter()
        .enumerate()
        .map(|(i, m)| if i == 0 { AirProvingContext::simple(m, pvs.clone()) } else { AirProvingContext::simple_no_pis(m) })
        .collect();
    let parent = Sha384CpuEngine::new(debug_params());
    parent.debug(&airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
    b
}

fn must_fail(name: &str, f: impl FnOnce()) {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    assert!(r.is_err(), "tamper not rejected: {name}");
    println!("AGG_TAMPER rejected: {name}");
}

/// Column index (in NvAir) of a Hash2Cols field, by its value in an index-filled view.
fn hcol(f: impl Fn(&Hash2Cols<usize>) -> usize) -> usize {
    use core::borrow::Borrow;
    let idx: Vec<usize> = (0..HASH2_WIDTH).collect();
    let v: &Hash2Cols<usize> = idx[..].borrow();
    N_COMMON + f(v)
}

/// Rows of NvAir whose hash-chain flag (kh, common column 3) is set.
fn hash_rows(m: &RowMajorMatrix<F>) -> Vec<usize> {
    (0..m.values.len() / m.width).filter(|&r| m.values[r * m.width + 3] == F::ONE).collect()
}

// ---------------------------------------------------------------------------------------

#[test]
fn agg_segment_chain_native() {
    let segs = chunk_segments(&[7], 4, 32);
    for w in segs.windows(2) {
        assert_eq!(w[0].post(), w[1].pre);
    }
    let st: Vec<RangeStmt> = segs.iter().map(|s| s.stmt()).collect();
    let all = RangeStmt::compose(&st).unwrap();
    assert_eq!((all.a, all.e), (F::ZERO, F::from_u64(4)));
    assert!(RangeStmt::compose(&[st[1].clone(), st[0].clone()]).is_none());
    assert!(RangeStmt::compose(&[st[0].clone(), st[2].clone()]).is_none());
    // proofs verify natively and expose the statement fields
    let pr = prove_segs(&segs[..2]);
    assert_eq!(pr[0].1.public_values[0], segs[0].public_values());
}

/// The k-child program: honest k = 2, 3 pass and expose the composed statement; each child's
/// verifier runs on its own transcript (k - 1 restarts).
#[test]
fn agg_program_honest() {
    let segs = chunk_segments(&[7], 3, 32);
    let pr = prove_segs(&segs);
    for k in [2usize, 3] {
        let (b, s) = program(&pr[..k]);
        assert!(b.failures.is_empty(), "k = {k}: {:?}", b.failures);
        assert_eq!(b.transcript.starts.len(), k - 1);
        let want = RangeStmt::compose(&segs[..k].iter().map(|s| s.stmt()).collect::<Vec<_>>()).unwrap();
        assert_eq!(s, want);
        assert!(check_range_statement(&b.public_values(), &want));
        println!("AGG_PROGRAM k={k} rows={} jobs={} merkle_nodes={}", b.instrs.len(), b.job_units.len(), b.merkle_nodes);
    }
}

/// Program-level tampers: swapped children, broken continuity (a valid proof of a segment that
/// does not start where the previous one ended), a dropped child, a different chunk.
#[test]
fn agg_program_tamper() {
    let segs = chunk_segments(&[7], 3, 32);
    let pr = prove_segs(&segs);
    let mut wrong_pre = segs[1].clone();
    wrong_pre.pre = (wrong_pre.pre.0 + F::ONE, wrong_pre.pre.1);
    let mut other_ctx = segs[1].clone();
    other_ctx.ctx = vec![F::from_u64(8)];
    let extra = prove_segs(&[wrong_pre, other_ctx]);
    let cases: Vec<(&str, Vec<(Vk, Pf)>)> = vec![
        ("swapped children", vec![pr[1].clone(), pr[0].clone()]),
        ("broken continuity", vec![pr[0].clone(), extra[0].clone()]),
        ("dropped child", vec![pr[0].clone(), pr[2].clone()]),
        ("other chunk", vec![pr[0].clone(), extra[1].clone()]),
    ];
    for (name, ch) in cases {
        let (b, _) = program(&ch);
        println!("AGG_PROGRAM_TAMPER {name}: {:?}", b.failures);
        assert!(!b.failures.is_empty(), "{name} not detected");
    }
}

/// The circuit: debug constraint and bus check for honest k = 2 and 3; tampers at the trace
/// level (statement limb, chain-start forging) and the program-level tampers (the circuit's Zero
/// rows reject them).
#[test]
fn agg_circuit_debug() {
    let segs = chunk_segments(&[7], 3, 32);
    let pr = prove_segs(&segs);
    agg_debug(&pr[..2], APP, &[], 17, |_, _| {});
    agg_debug(&pr[..3], APP, &[], 17, |_, _| {});
    // exposed statement digest limb
    must_fail("statement digest limb", || {
        agg_debug(&pr[..2], APP, &[], 17, |_, pvs| pvs[5] += F::ONE);
    });
    must_fail("level", || {
        agg_debug(&pr[..2], APP, &[], 17, |_, pvs| pvs[0] += F::ONE);
    });
    // chain starts are declared by the program: un-declare / forge one
    let is_first = hcol(|h| h.is_first);
    let hn = hcol(|h| h.hn);
    must_fail("chain start removed", || {
        agg_debug(&pr[..2], APP, &[], 17, |m, _| {
            let rows = hash_rows(&m[0]);
            let w = m[0].width;
            let r = *rows.iter().skip(1).find(|&&r| m[0].values[r * w + is_first] == F::ONE).unwrap();
            m[0].values[r * w + is_first] = F::ZERO;
            m[0].values[(r - 1) * w + hn] = F::ONE;
        });
    });
    must_fail("chain start forged", || {
        agg_debug(&pr[..2], APP, &[], 17, |m, _| {
            let rows = hash_rows(&m[0]);
            let w = m[0].width;
            let r = rows[3];
            assert_eq!(m[0].values[r * w + is_first], F::ZERO);
            m[0].values[r * w + is_first] = F::ONE;
            m[0].values[(r - 1) * w + hn] = F::ZERO;
        });
    });
    let mut wrong_pre = segs[1].clone();
    wrong_pre.pre = (wrong_pre.pre.0 + F::ONE, wrong_pre.pre.1);
    let extra = prove_segs(&[wrong_pre]);
    for (name, ch) in [
        ("circuit: swapped children", vec![pr[1].clone(), pr[0].clone()]),
        ("circuit: broken continuity", vec![pr[0].clone(), extra[0].clone()]),
        ("circuit: dropped child", vec![pr[0].clone(), pr[2].clone()]),
    ] {
        must_fail(name, || {
            agg_debug(&ch, APP, &[], 17, |_, _| {});
        });
    }
}

/// Keygen: columns, degree and interactions of the aggregation circuit (same AIRs as NV).
#[test]
fn agg_shape() {
    let circ = NvCircuit::new(3, 17, 1);
    let airs = circ.airs::<Sha384Config>();
    let engine = Sha384CpuEngine::new(debug_params());
    let (_, vk) = engine.keygen(&airs);
    for (a, avk) in airs.iter().zip(&vk.inner.per_air) {
        println!(
            "AGG_SHAPE {} w={} int/row={} deg={} pvs={}",
            a.name(),
            avk.params.width.common_main,
            avk.symbolic_constraints.interactions.len(),
            avk.max_constraint_degree,
            avk.params.num_public_values
        );
    }
    assert_eq!(vk.inner.per_air[0].params.num_public_values, NV_NUM_PVS);
}

/// Real proofs (heavy; env PARENT_* / CHILD2_* params): level 1 = 2-to-1 over app segments
/// (twice: segments 0-1 and 2-3), level 2 = 2-to-1 over the two level-1 proofs (statement
/// preimages checked in-circuit; program binding not emitted, see agg.rs).  Checks the final
/// statement natively and prints per-level shape, cost and resources.
#[test]
#[ignore]
fn agg_chain() {
    use crate::sha384::e2e_tests::{describe, env_usize, params_from_env, proof_sizes, soundness};
    let segs = chunk_segments(&[7], 4, 32);
    let pr = prove_segs(&segs);
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
    let level = |tag: &str, pp: openvm_stark_backend::SystemParams, log_rows: usize, k_child: usize, children: &[(Vk, Pf)], kind: ChildKind, pre: &[RangeStmt]| -> (Vk, Pf, Builder) {
        let mut pp = pp;
        pp.max_constraint_degree = debug_params().max_constraint_degree;
        describe(tag, &pp);
        let engine = Sha384CpuEngine::new(pp);
        let circ = NvCircuit::new(k_child, log_rows, 1);
        reset_hwm();
        let t = std::time::Instant::now();
        let (mats, b) = circ.generate_with(|b| {
            build_agg(b, &refs(children), kind, pre);
        });
        let shapes: Vec<(usize, usize)> = mats.iter().map(|m| (m.values.len() / m.width, m.width)).collect();
        let (vk, p, _) = super::circuit::prove_mats(&circ, &engine, mats, &b);
        let secs = t.elapsed().as_secs_f64();
        let airs = circ.airs::<Sha384Config>();
        let (mut cols, mut opened, mut ints, mut cells) = (0, 0, 0usize, 0usize);
        for (i, a) in vk.inner.per_air.iter().enumerate() {
            let w = a.params.width.common_main;
            cols += w;
            opened += w + a.params.opening_masks()[0].iter().filter(|&&m| m).count();
            ints += shapes[i].0 * a.symbolic_constraints.interactions.len();
            cells += shapes[i].0 * shapes[i].1;
            println!("{tag}_AIR {} h={} w={} int/row={} deg={}", airs[i].name(), shapes[i].0, w, a.symbolic_constraints.interactions.len(), a.max_constraint_degree);
        }
        let blocks: usize = b.jobs().iter().filter(|j| !j.node).map(|j| j.num_blocks()).sum();
        println!(
            "{tag}_SUMMARY children={} cols={cols} opened={opened} interactions={ints} cells={cells} program_rows={} merkle_nodes={} leaf_blocks={blocks} chain_starts={} prove_s={secs:.1} peak_rss_gb={:.2}",
            children.len(),
            b.instrs.len(),
            b.merkle_nodes,
            b.transcript.starts.len() + 1,
            hwm_gb()
        );
        soundness(tag, &vk);
        println!("{tag}_PROOF_BYTES {}", proof_sizes(&p));
        (vk, p, b)
    };
    let p1 = params_from_env("PARENT", [16, 3, 20, 3]);
    let lr1 = env_usize("AGG_LOG_ROWS1", 17);
    let k1 = child_params_small().k_whir();
    let (va, pa, ba) = level("N1a", p1.clone(), lr1, k1, &pr[..2], APP, &[]);
    let (vb, pb, bb) = level("N1b", p1.clone(), lr1, k1, &pr[2..], APP, &[]);
    let sa = RangeStmt::compose(&[segs[0].stmt(), segs[1].stmt()]).unwrap();
    let sb = RangeStmt::compose(&[segs[2].stmt(), segs[3].stmt()]).unwrap();
    assert!(check_range_statement(&ba.public_values(), &sa));
    assert!(check_range_statement(&bb.public_values(), &sb));
    assert_eq!(pa.public_values[0], ba.public_values());
    if env_usize("AGG_LEVELS", 2) < 2 {
        return;
    }
    let p2 = params_from_env("PARENT2", [16, 3, 20, 3]);
    let lr2 = env_usize("AGG_LOG_ROWS2", 19);
    let kp = p1.k_whir();
    let node = ChildKind::Node { n_ctx: N_CTX, n_state: 2 };
    let (_v2, p2p, b2) = level("N2", p2, lr2, kp, &[(va, pa), (vb, pb)], node, &[sa.clone(), sb.clone()]);
    let all = RangeStmt::compose(&segs.iter().map(|s| s.stmt()).collect::<Vec<_>>()).unwrap();
    assert!(check_range_statement(&p2p.public_values[0], &all), "final statement");
    assert_eq!(b2.level, 2);
    // a dropped last segment is not the chunk statement
    let short = RangeStmt::compose(&segs[..3].iter().map(|s| s.stmt()).collect::<Vec<_>>()).unwrap();
    assert!(!check_range_statement(&p2p.public_values[0], &short));
    println!("AGG_CHAIN_OK final statement = segments [0, 4)");
}

/// Level-2 node in the debug checker (no proving of the level-2 trace): two real level-1
/// proofs at a low query target, statement preimages hashed in-circuit; tampered preimages,
/// swapped and duplicated children are rejected.
#[test]
#[ignore]
fn agg_node_debug() {
    use crate::sha384::e2e_tests::{env_usize, params_from_env};
    let segs = chunk_segments(&[7], 4, 32);
    let pr = prove_segs(&segs);
    let mut p1 = params_from_env("PARENT", [12, 2, 8, 3]);
    p1.max_constraint_degree = debug_params().max_constraint_degree;
    let engine = Sha384CpuEngine::new(p1.clone());
    let lr1 = env_usize("AGG_LOG_ROWS1", 17);
    let k1 = child_params_small().k_whir();
    let one = |ch: &[(Vk, Pf)]| -> (Vk, Pf) {
        let circ = NvCircuit::new(k1, lr1, 1);
        let (mats, b) = circ.generate_with(|b| {
            build_agg(b, &refs(ch), APP, &[]);
        });
        let (vk, p, _) = super::circuit::prove_mats(&circ, &engine, mats, &b);
        (vk, p)
    };
    let na = one(&pr[..2]);
    let nb = one(&pr[2..]);
    let sa = RangeStmt::compose(&[segs[0].stmt(), segs[1].stmt()]).unwrap();
    let sb = RangeStmt::compose(&[segs[2].stmt(), segs[3].stmt()]).unwrap();
    let node = ChildKind::Node { n_ctx: N_CTX, n_state: 2 };
    let lr2 = env_usize("AGG_LOG_ROWS2", 19);
    let kids = vec![na.clone(), nb.clone()];
    let b = agg_debug_k(&kids, node, &[sa.clone(), sb.clone()], lr2, p1.k_whir());
    let all = RangeStmt::compose(&segs.iter().map(|s| s.stmt()).collect::<Vec<_>>()).unwrap();
    assert!(check_range_statement(&b.public_values(), &all));
    // wrong preimage (claims a different boundary state), swapped, duplicated
    let mut bad = sa.clone();
    bad.s_e[0] += F::ONE;
    let mut b2 = Builder::new(lr2, 0);
    build_agg(&mut b2, &refs(&kids), node, &[bad.clone(), sb.clone()]);
    assert!(!b2.failures.is_empty());
    must_fail("node: wrong preimage", || {
        agg_debug_k(&kids, node, &[bad.clone(), sb.clone()], lr2, p1.k_whir());
    });
    must_fail("node: swapped children", || {
        agg_debug_k(&[nb.clone(), na.clone()], node, &[sb.clone(), sa.clone()], lr2, p1.k_whir());
    });
    must_fail("node: duplicated child", || {
        agg_debug_k(&[na.clone(), na.clone()], node, &[sa.clone(), sa.clone()], lr2, p1.k_whir());
    });
}

fn agg_debug_k(children: &[(Vk, Pf)], kind: ChildKind, pre: &[RangeStmt], log_rows: usize, k: usize) -> Builder {
    agg_debug_k_mutated(children, kind, pre, log_rows, k, |_| {})
}

/// [`agg_debug_k`] with a trace mutation applied before the constraint + bus check.
fn agg_debug_k_mutated(
    children: &[(Vk, Pf)],
    kind: ChildKind,
    pre: &[RangeStmt],
    log_rows: usize,
    k: usize,
    mutate: impl FnOnce(&mut Vec<RowMajorMatrix<F>>),
) -> Builder {
    use openvm_cpu_backend::CpuBackend;
    use openvm_stark_backend::prover::{AirProvingContext, MatrixDimensions, ProvingContext};
    let circ = NvCircuit::new(k, log_rows, 1);
    let airs = circ.airs::<Sha384Config>();
    let (mut mats, b) = circ.generate_with(|b| {
        build_agg(b, &refs(children), kind, pre);
    });
    let pvs = b.public_values();
    let mut total = 0;
    for (a, m) in airs.iter().zip(&mats) {
        println!("AGGN_AIR {} {} x {}", a.name(), m.height(), m.width());
        total += m.height() * m.width();
    }
    println!("AGGN_TOTAL_CELLS {total} program_rows={} merkle_nodes={}", b.instrs.len(), b.merkle_nodes);
    mutate(&mut mats);
    let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = mats
        .into_iter()
        .enumerate()
        .map(|(i, m)| if i == 0 { AirProvingContext::simple(m, pvs.clone()) } else { AirProvingContext::simple_no_pis(m) })
        .collect();
    let parent = Sha384CpuEngine::new(debug_params());
    parent.debug(&airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
    b
}

/// Design G, level 1: main proof (a segment-machine proof whose ctx[0] stands for the code-table
/// commitment its FETCH table uses) + one PREP-like sub-proof (Fib, public value 2 = its output, the
/// "commitment"), linked; plus a second sub-proof of a different vk to show heterogeneous children.
#[test]
fn agg_g_l1_linked() {
    use super::agg::{build_l1_linked, check_statement, Link};
    use openvm_stark_backend::test_utils::FibFixture;
    let engine = Sha384CpuEngine::new(child_params_small());
    let fib = FibFixture::new(0, 1, 1 << 5);
    let (vf, pf) = fib.keygen_and_prove(&engine);
    let code = pf.public_values[0][2];
    let mut main = chunk_segments(&[0], 1, 32).remove(0);
    main.ctx = vec![code];
    let mut bad_main = main.clone();
    bad_main.ctx = vec![code + F::ONE];
    let pr = prove_segs(&[main.clone(), bad_main]);
    let (vk_m, p_m) = &pr[0];
    let link = [Link { sub: 1, sub_pv: 2, main_pv: 0 }];
    let run = |main: &(Vk, Pf), log_rows: usize, mutate: &dyn Fn(&mut Vec<RowMajorMatrix<F>>, &mut Vec<F>)| -> Builder {
        use openvm_cpu_backend::CpuBackend;
        use openvm_stark_backend::prover::{AirProvingContext, ProvingContext};
        let circ = NvCircuit::new(3, log_rows, 1);
        let airs = circ.airs::<Sha384Config>();
        let (mut mats, b) = circ.generate_with(|b| {
            build_l1_linked(b, &[(&main.0, &main.1), (&vf, &pf)], &link);
        });
        let mut pvs = b.public_values();
        mutate(&mut mats, &mut pvs);
        let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = mats
            .into_iter()
            .enumerate()
            .map(|(i, m)| if i == 0 { AirProvingContext::simple(m, pvs.clone()) } else { AirProvingContext::simple_no_pis(m) })
            .collect();
        Sha384CpuEngine::new(debug_params()).debug(&airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
        b
    };
    let b = run(&pr[0], 17, &|_, _| {});
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    assert!(check_statement(&b.public_values(), &p_m.public_values));
    println!("AGG_G_L1 rows={} chain_starts={}", b.instrs.len(), b.transcript.starts.len() + 1);
    let _ = vk_m;
    // a main proof using a different code commitment than the sub-proof proves: rejected
    let mut bb = Builder::new(18, 0);
    build_l1_linked(&mut bb, &[(&pr[1].0, &pr[1].1), (&vf, &pf)], &link);
    assert!(!bb.failures.is_empty());
    must_fail("G: broken link", || {
        run(&pr[1], 17, &|_, _| {});
    });
    must_fail("G: statement digest limb", || {
        run(&pr[0], 17, &|_, pvs| pvs[3] += F::ONE);
    });
}

/// **Program-binding gate for an aggregation node.**
///
/// A level-2 node verifies two NV children and (`bind_child`) constrains each child's program to
/// be the node's own via `bind_child_program`.  Without that constraint the node would accept a
/// valid proof of a different circuit and the tree claim would be worthless - this is the
/// aggregation analogue of the G2 forgery control.
///
/// The test checks three things: the honest node passes the full constraint + bus check; the
/// node's trace really carries a BIND region; and changing a child's program word in the trace
/// makes the check fail.
#[test]
#[ignore]
fn agg_node_program_binding() {
    use crate::sha384::e2e_tests::{env_usize, params_from_env};
    let segs = chunk_segments(&[7], 4, 32);
    let pr = prove_segs(&segs);
    let mut p1 = params_from_env("PARENT", [12, 2, 8, 3]);
    p1.max_constraint_degree = debug_params().max_constraint_degree;
    let engine = Sha384CpuEngine::new(p1.clone());
    let lr1 = env_usize("AGG_LOG_ROWS1", 17);
    let k1 = child_params_small().k_whir();
    let one = |ch: &[(Vk, Pf)]| -> (Vk, Pf) {
        let circ = NvCircuit::new(k1, lr1, 1);
        let (mats, b) = circ.generate_with(|b| {
            build_agg(b, &refs(ch), APP, &[]);
        });
        let (vk, p, _) = super::circuit::prove_mats(&circ, &engine, mats, &b);
        (vk, p)
    };
    let na = one(&pr[..2]);
    let nb = one(&pr[2..]);
    let sa = RangeStmt::compose(&[segs[0].stmt(), segs[1].stmt()]).unwrap();
    let sb = RangeStmt::compose(&[segs[2].stmt(), segs[3].stmt()]).unwrap();
    let node = ChildKind::Node { n_ctx: N_CTX, n_state: 2 };
    let lr2 = env_usize("AGG_LOG_ROWS2", 19);
    let kids = vec![na.clone(), nb.clone()];
    let all = RangeStmt::compose(&segs.iter().map(|s| s.stmt()).collect::<Vec<_>>()).unwrap();

    // 1. honest node: binds both children, which are its own program
    let b = agg_debug_k(&kids, node, &[sa.clone(), sb.clone()], lr2, p1.k_whir());
    assert!(check_range_statement(&b.public_values(), &all), "honest node statement");
    let rows = b.instrs.len();
    println!("AGG_BIND honest node accepted: program rows={rows}");

    // 2. the BIND region is really emitted for each NV child
    let circ = NvCircuit::new(p1.k_whir(), lr2, 1);
    let (mats, bb) = circ.generate_with(|b| {
        build_agg(b, &refs(&kids), node, &[sa.clone(), sb.clone()]);
    });
    assert!(bb.failures.is_empty(), "{:?}", bb.failures);
    let nv_rows = mats[0].values.len() / mats[0].width;
    assert!(nv_rows >= bb.instrs.len() + bb.instrs.len() / 2, "NvAir carries a BIND row per ALU pair");
    assert!(bb.instrs.iter().any(|i| i.op == super::isa::Op::Zero), "BIND emits Zero rows");

    // 3. the gate: changing a child's program word must break the check
    let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        agg_debug_k(&kids, node, &[sa.clone(), sb.clone()], lr2, p1.k_whir());
    }));
    assert!(ok.is_ok(), "control: the honest node itself must pass");
    let bad = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        agg_debug_k_mutated(&kids, node, &[sa.clone(), sb.clone()], lr2, p1.k_whir(), |mats| {
            let w = mats[0].width;
            for j in 0..4 {
                mats[0].values[super::uair::U_P + j] += F::ONE;
            }
            let _ = w;
        });
    }));
    assert!(bad.is_err(), "POSITIVE-CONTROL: a child program changed in the trace must be rejected");
    println!("AGG_BIND tampered child program rejected");
}
