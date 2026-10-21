//! pq-nv-preprocessed demo: a toy base layer in the pq-wasm-base FETCH style whose code table
//! (records [pc, op, h, fee, x0..x3]) and byte range table are preprocessed, verified by NV.
//! Variants (DESIGN.md §6):
//!   * `Split`: CODE and RANGE are two preprocessed AIRs (3 commitments: main + 2 preprocessed);
//!   * `Fixed`: one FIXED AIR holds both tables as preprocessed columns (2 commitments);
//!   * `Public`: the pq-wasm-base design today: code records are public values, one boundary
//!     interaction per record; RANGE is committed and derived (1 commitment).
use std::sync::Arc;

use openvm_stark_backend::{
    interaction::{InteractionBuilder, LookupBus},
    prover::{AirProvingContext, ColMajorMatrix, CpuColMajorBackend, ProvingContext},
    test_utils::TestFixture,
    AirRef, BaseAirWithPublicValues, PartitionedBaseAir, StarkEngine,
};
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PairBuilder};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use super::{builder::Builder, verifier::build_verifier};
use crate::sha384::{config::*, e2e_tests::child_params_small};

const FETCH: LookupBus = LookupBus::new(0);
const RANGE: LookupBus = LookupBus::new(1);
/// code record width (pq-wasm-base FETCH message)
const REC: usize = 8;
const RANGE_ROWS: usize = 256;

fn records(n: usize) -> Vec<[u32; REC]> {
    (0..n as u32).map(|i| [i, i % 3, i % 5, 1 + i % 2, 3 * i + 1, i, 2 * i, 7]).collect()
}

// ---- CODE: preprocessed [rec(8), valid], main [mult] ----
pub struct CodeAir {
    pub code: Vec<[u32; REC]>,
    pub rows: usize,
}
impl<F: Field> BaseAir<F> for CodeAir {
    fn width(&self) -> usize {
        1
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let mut v = vec![F::ZERO; self.rows * (REC + 1)];
        for (i, r) in self.code.iter().enumerate() {
            for k in 0..REC {
                v[i * (REC + 1) + k] = F::from_u32(r[k]);
            }
            v[i * (REC + 1) + REC] = F::ONE;
        }
        Some(RowMajorMatrix::new(v, REC + 1))
    }
}
impl<F: Field> BaseAirWithPublicValues<F> for CodeAir {}
impl<F: Field> PartitionedBaseAir<F> for CodeAir {}
impl<AB: AirBuilderWithPublicValues + PairBuilder + InteractionBuilder> Air<AB> for CodeAir {
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let p = prep.row_slice(0).unwrap();
        let main = builder.main();
        let m = main.row_slice(0).unwrap();
        let mult: AB::Expr = m[0].clone().into();
        let valid: AB::Expr = p[REC].clone().into();
        // padding rows (valid = 0) offer nothing
        builder.assert_zero(mult.clone() * (AB::Expr::ONE - valid));
        let key: Vec<AB::Expr> = (0..REC).map(|k| p[k].clone().into()).collect();
        FETCH.add_key_with_lookups(builder, key, mult);
    }
}

// ---- RANGE: preprocessed [v = row], main [mult] ----
pub struct RangeAir;
impl<F: Field> BaseAir<F> for RangeAir {
    fn width(&self) -> usize {
        1
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(RowMajorMatrix::new_col((0..RANGE_ROWS).map(F::from_usize).collect()))
    }
}
impl<F: Field> BaseAirWithPublicValues<F> for RangeAir {}
impl<F: Field> PartitionedBaseAir<F> for RangeAir {}
impl<AB: AirBuilderWithPublicValues + PairBuilder + InteractionBuilder> Air<AB> for RangeAir {
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let v: AB::Expr = prep.row_slice(0).unwrap()[0].clone().into();
        let main = builder.main();
        let mult: AB::Expr = main.row_slice(0).unwrap()[0].clone().into();
        RANGE.add_key_with_lookups(builder, vec![v], mult);
    }
}

// ---- FIXED: both tables in one preprocessed trace (256 rows): [rec(8), valid, v], main [mc, mr] ----
pub struct FixedAir {
    pub code: Vec<[u32; REC]>,
}
impl<F: Field> BaseAir<F> for FixedAir {
    fn width(&self) -> usize {
        2
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let w = REC + 2;
        let mut v = vec![F::ZERO; RANGE_ROWS * w];
        for i in 0..RANGE_ROWS {
            if let Some(r) = self.code.get(i) {
                for k in 0..REC {
                    v[i * w + k] = F::from_u32(r[k]);
                }
                v[i * w + REC] = F::ONE;
            }
            v[i * w + REC + 1] = F::from_usize(i);
        }
        Some(RowMajorMatrix::new(v, w))
    }
}
impl<F: Field> BaseAirWithPublicValues<F> for FixedAir {}
impl<F: Field> PartitionedBaseAir<F> for FixedAir {}
impl<AB: AirBuilderWithPublicValues + PairBuilder + InteractionBuilder> Air<AB> for FixedAir {
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let p = prep.row_slice(0).unwrap();
        let main = builder.main();
        let m = main.row_slice(0).unwrap();
        let (mc, mr): (AB::Expr, AB::Expr) = (m[0].clone().into(), m[1].clone().into());
        let valid: AB::Expr = p[REC].clone().into();
        builder.assert_zero(mc.clone() * (AB::Expr::ONE - valid));
        let key: Vec<AB::Expr> = (0..REC).map(|k| p[k].clone().into()).collect();
        FETCH.add_key_with_lookups(builder, key, mc);
        RANGE.add_key_with_lookups(builder, vec![p[REC + 1].clone().into()], mr);
    }
}

// ---- BOUNDARY (Public variant): code records as public values, one interaction per record ----
pub struct BoundaryAir {
    pub n: usize,
}
impl<F: Field> BaseAir<F> for BoundaryAir {
    fn width(&self) -> usize {
        self.n
    }
}
impl<F: Field> BaseAirWithPublicValues<F> for BoundaryAir {
    fn num_public_values(&self) -> usize {
        REC * self.n
    }
}
impl<F: Field> PartitionedBaseAir<F> for BoundaryAir {}
impl<AB: AirBuilderWithPublicValues + PairBuilder + InteractionBuilder> Air<AB> for BoundaryAir {
    fn eval(&self, builder: &mut AB) {
        let pv: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let main = builder.main();
        let m = main.row_slice(0).unwrap();
        let mults: Vec<AB::Expr> = (0..self.n).map(|j| m[j].clone().into()).collect();
        // records are offered on the first row only (pq-wasm-base: count first * mult_j)
        let first: AB::Expr = builder.is_first_row();
        for (j, mult) in mults.into_iter().enumerate() {
            builder.assert_zero((AB::Expr::ONE - first.clone()) * mult.clone());
            FETCH.add_key_with_lookups(builder, pv[REC * j..REC * (j + 1)].to_vec(), mult);
        }
    }
}

/// RANGE committed and derived (Public variant): main [v, mult], v_0 = 0, v' = v + 1.
pub struct RangeCommittedAir;
impl<F: Field> BaseAir<F> for RangeCommittedAir {
    fn width(&self) -> usize {
        2
    }
}
impl<F: Field> BaseAirWithPublicValues<F> for RangeCommittedAir {}
impl<F: Field> PartitionedBaseAir<F> for RangeCommittedAir {}
impl<AB: AirBuilderWithPublicValues + PairBuilder + InteractionBuilder> Air<AB> for RangeCommittedAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let (l, n) = (main.row_slice(0).unwrap(), main.row_slice(1).unwrap());
        let (v, mult, nv): (AB::Expr, AB::Expr, AB::Expr) = (l[0].clone().into(), l[1].clone().into(), n[0].clone().into());
        builder.when_first_row().assert_zero(v.clone());
        builder.when_transition().assert_eq(nv, v.clone() + AB::Expr::ONE);
        builder.when_last_row().assert_eq(v.clone(), AB::Expr::from_usize(RANGE_ROWS - 1));
        RANGE.add_key_with_lookups(builder, vec![v], mult);
    }
}

// ---- EXEC: main [real, rec(8), byte, acc]: fetch the record at pc, acc' = acc + x0 + byte ----
pub struct ExecAir;
const E_REAL: usize = 0;
const E_REC: usize = 1;
const E_BYTE: usize = 1 + REC;
const E_ACC: usize = 2 + REC;
const E_W: usize = 3 + REC;
impl<F: Field> BaseAir<F> for ExecAir {
    fn width(&self) -> usize {
        E_W
    }
}
impl<F: Field> BaseAirWithPublicValues<F> for ExecAir {
    fn num_public_values(&self) -> usize {
        1
    }
}
impl<F: Field> PartitionedBaseAir<F> for ExecAir {}
impl<AB: AirBuilderWithPublicValues + PairBuilder + InteractionBuilder> Air<AB> for ExecAir {
    fn eval(&self, builder: &mut AB) {
        let out: AB::Expr = builder.public_values()[0].into();
        let main = builder.main();
        let (l, n) = (main.row_slice(0).unwrap(), main.row_slice(1).unwrap());
        let e = |r: &[AB::Var], i: usize| -> AB::Expr { r[i].clone().into() };
        let (real, pc, x0, byte, acc) = (e(&l, E_REAL), e(&l, E_REC), e(&l, E_REC + 4), e(&l, E_BYTE), e(&l, E_ACC));
        let (nreal, npc, nacc) = (e(&n, E_REAL), e(&n, E_REC), e(&n, E_ACC));
        builder.assert_bool(real.clone());
        builder.when_first_row().assert_one(real.clone());
        builder.when_first_row().assert_zero(pc.clone());
        builder.when_first_row().assert_zero(acc.clone());
        // real rows form a prefix; within it pc' = pc + 1, acc' = acc + x0 + byte
        builder.when_transition().assert_zero(nreal.clone() * (AB::Expr::ONE - real.clone()));
        builder.when_transition().assert_zero(nreal.clone() * (npc - pc.clone() - AB::Expr::ONE));
        builder.when_transition().assert_zero(nreal.clone() * (nacc.clone() - acc.clone() - x0.clone() - byte.clone()));
        // the last real row's acc + x0 + byte is the output
        let fin = acc + x0 + byte.clone();
        builder.when_transition().assert_zero(real.clone() * (AB::Expr::ONE - nreal) * (fin.clone() - out.clone()));
        builder.when_last_row().assert_zero(real.clone() * (fin - out));
        let key: Vec<AB::Expr> = (0..REC).map(|k| e(&l, E_REC + k)).collect();
        FETCH.lookup_key(builder, key, real.clone());
        RANGE.lookup_key(builder, vec![byte], real);
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Variant {
    Split,
    Fixed,
    Public,
}

/// Toy base: `n` code records, `steps` executed (pc 0..steps), EXEC height `exec_rows`.
pub struct ToyBase {
    pub v: Variant,
    pub n: usize,
    pub steps: usize,
    pub exec_rows: usize,
    pub seed: u64,
}

impl ToyBase {
    fn code(&self) -> Vec<[u32; REC]> {
        records(self.n)
    }
    fn bytes(&self) -> Vec<u32> {
        // byte 255 is always used, so the RANGE multiplicity column has no zero tail (tight heights
        // lever: the committed height would otherwise depend on the execution)
        (0..self.steps as u64).map(|i| if i == 0 { 255 } else { ((i * 37 + self.seed * 11) % 256) as u32 }).collect()
    }
    fn exec(&self) -> (RowMajorMatrix<F>, F) {
        let code = self.code();
        let bytes = self.bytes();
        let mut v = vec![F::ZERO; self.exec_rows * E_W];
        let mut acc = F::ZERO;
        for i in 0..self.steps {
            let r = &mut v[i * E_W..(i + 1) * E_W];
            r[E_REAL] = F::ONE;
            for k in 0..REC {
                r[E_REC + k] = F::from_u32(code[i][k]);
            }
            r[E_BYTE] = F::from_u32(bytes[i]);
            r[E_ACC] = acc;
            acc += F::from_u32(code[i][4]) + F::from_u32(bytes[i]);
        }
        (RowMajorMatrix::new(v, E_W), acc)
    }
    fn range_mults(&self) -> Vec<F> {
        let mut m = vec![F::ZERO; RANGE_ROWS];
        for b in self.bytes() {
            m[b as usize] += F::ONE;
        }
        m
    }
    fn code_rows(&self) -> usize {
        self.n.next_power_of_two().max(4)
    }
}

fn ctx(m: RowMajorMatrix<F>, pv: Vec<F>) -> AirProvingContext<CpuColMajorBackend<Sha384Config>> {
    AirProvingContext::simple(ColMajorMatrix::from_row_major(&m), pv)
}

impl TestFixture<Sha384Config> for ToyBase {
    fn airs(&self) -> Vec<AirRef<Sha384Config>> {
        match self.v {
            Variant::Split => vec![Arc::new(ExecAir), Arc::new(CodeAir { code: self.code(), rows: self.code_rows() }), Arc::new(RangeAir)],
            Variant::Fixed => vec![Arc::new(ExecAir), Arc::new(FixedAir { code: self.code() })],
            Variant::Public => vec![Arc::new(ExecAir), Arc::new(BoundaryAir { n: self.n }), Arc::new(RangeCommittedAir)],
        }
    }
    fn generate_proving_ctx(&self) -> ProvingContext<CpuColMajorBackend<Sha384Config>> {
        let (exec, out) = self.exec();
        let rm = self.range_mults();
        // every record is fetched once (steps = n) or not at all
        let cm = |i: usize| F::from_bool(i < self.steps.min(self.n));
        let mut ctxs = vec![(0, ctx(exec, vec![out]))];
        match self.v {
            Variant::Split => {
                ctxs.push((1, ctx(RowMajorMatrix::new_col((0..self.code_rows()).map(cm).collect()), vec![])));
                ctxs.push((2, ctx(RowMajorMatrix::new_col(rm), vec![])));
            }
            Variant::Fixed => {
                let v = (0..RANGE_ROWS).flat_map(|i| [cm(i), rm[i]]).collect();
                ctxs.push((1, ctx(RowMajorMatrix::new(v, 2), vec![])));
            }
            Variant::Public => {
                let mut v = vec![F::ZERO; 4 * self.n];
                for j in 0..self.n {
                    v[j] = cm(j);
                }
                let pv = self.code().iter().flatten().map(|&x| F::from_u32(x)).collect();
                ctxs.push((1, ctx(RowMajorMatrix::new(v, self.n), pv)));
                let rv = (0..RANGE_ROWS).flat_map(|i| [F::from_usize(i), rm[i]]).collect();
                ctxs.push((2, ctx(RowMajorMatrix::new(rv, 2), vec![])));
            }
        }
        ProvingContext::new(ctxs)
    }
}

fn nv_debug(vk: &openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<Sha384Config>, proof: &openvm_stark_backend::proof::Proof<Sha384Config>, log_rows: usize) {
    use openvm_cpu_backend::CpuBackend;
    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), log_rows, 1);
    let airs = circ.airs::<Sha384Config>();
    let (mats, b) = circ.generate(vk, proof);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
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

/// The toy base in all three variants: native verify, NV program (no failures, native
/// transcript, witness-independent), full NV constraint check; program rows per variant and
/// code size (the Public variant grows with the code, the preprocessed ones do not).
#[test]
fn nv_prep_demo_toy_base() {
    let e = Sha384CpuEngine::new(child_params_small());
    let mut table = vec![];
    for v in [Variant::Public, Variant::Split, Variant::Fixed] {
        for n in [16usize, 32, 64] {
            let fx = ToyBase { v, n, steps: n, exec_rows: 64, seed: 1 };
            let (vk, proof) = fx.keygen_and_prove(&e);
            e.verify(&vk, &proof).expect("native");
            let mut b = Builder::new(17, 0);
            build_verifier(&mut b, &vk, &proof);
            assert!(b.failures.is_empty(), "{v:?} n={n}: {:?}", b.failures);
            let mut t = ShaTranscript::default();
            openvm_stark_backend::verifier::verify(e.config(), &vk, &proof, &mut t).unwrap();
            assert_eq!(t.state, b.transcript.inner.state, "transcript");
            // a different execution (other bytes) of the same program: same NV program
            let (vk2, proof2) = ToyBase { seed: 5, ..fx }.keygen_and_prove(&e);
            let mut b2 = Builder::new(17, 0);
            build_verifier(&mut b2, &vk2, &proof2);
            assert!(b2.failures.is_empty());
            // (tight-heights lever: the committed heights are shape facts of the program; the two
            // executions must agree on them for the comparison to apply)
            let tight = |p: &openvm_stark_backend::proof::Proof<Sha384Config>| -> Vec<Option<usize>> {
                p.trace_vdata.iter().map(|v| v.as_ref().unwrap().tight_height).collect()
            };
            if tight(&proof) == tight(&proof2) {
                assert_eq!(b.instrs, b2.instrs, "program depends on the execution");
            } else {
                println!("NV_PREP_DEMO {v:?} n={n}: tight heights differ {:?} / {:?} (program comparison skipped)", tight(&proof), tight(&proof2));
            }
            let commits = proof.whir_proof.initial_round_opened_rows.len();
            let ints: usize = vk.inner.per_air.iter().map(|a| a.symbolic_constraints.interactions.len()).sum();
            println!(
                "NV_PREP_DEMO variant={v:?} n={n} commits={commits} interactions={ints} rows={} jobs={} merkle_nodes={} proof_bytes={}",
                b.instrs.len(),
                b.job_units.len(),
                b.merkle_nodes,
                bincode_len(&proof)
            );
            table.push((v, n, b.instrs.len()));
            if n == 32 {
                nv_debug(&vk, &proof, 16);
            }
        }
    }
    // preprocessed variants: rows independent of the code size (up to the deduplication of the
    // constant commitment's limbs against other program constants: a few rows)
    // (tight-heights lever: the code table's committed height is part of the shape; skip)
    let tight = e.params().whir.levers.tight_heights;
    for v in [Variant::Split, Variant::Fixed].into_iter().filter(|_| !tight) {
        let r: Vec<usize> = table.iter().filter(|x| x.0 == v).map(|x| x.2).collect();
        let (lo, hi) = (r.iter().min().unwrap(), r.iter().max().unwrap());
        assert!(hi - lo <= 24, "{v:?} rows depend on the code size: {r:?}");
    }
    // the public-value variant grows with the code
    let p: Vec<usize> = table.iter().filter(|x| x.0 == Variant::Public).map(|x| x.2).collect();
    assert!(p[0] < p[1] && p[1] < p[2]);
}

/// Program for (vk, proof) with failures.
fn prog(vk: &openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<Sha384Config>, proof: &openvm_stark_backend::proof::Proof<Sha384Config>) -> Vec<String> {
    let mut b = Builder::new(17, 0);
    build_verifier(&mut b, vk, proof);
    b.failures
}

/// The demo's soundness cases: an execution of a different program (same code size) is rejected by
/// the NV program for this code table (in-circuit too), and so is a forged proof whose EXEC
/// fetches a record the table does not contain (the native prover refuses to prove an unbalanced
/// bus, so the forgery is a tampered column opening of the code table).
#[test]
fn nv_prep_demo_wrong_program() {
    let e = Sha384CpuEngine::new(child_params_small());
    for v in [Variant::Split, Variant::Fixed] {
        let fx = ToyBase { v, n: 32, steps: 32, exec_rows: 64, seed: 1 };
        let (vk, proof) = fx.keygen_and_prove(&e);
        // a different program: record 3's x0 changed
        let other = |code: &mut Vec<[u32; REC]>| code[3][4] += 1;
        let (vk_o, proof_o) = {
            let fxo = ToyBaseOther { base: ToyBase { ..fx }, edit: other };
            fxo.keygen_and_prove(&e)
        };
        assert_ne!(vk.pre_hash, vk_o.pre_hash);
        e.verify(&vk_o, &proof_o).expect("the other program proves");
        assert!(e.verify(&vk, &proof_o).is_err());
        let f = prog(&vk, &proof_o);
        println!("NV_PREP_DEMO {v:?} other program under this program's NV: {} failures", f.len());
        assert!(!f.is_empty());
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| nv_debug_nofail(&vk, &proof_o, 16)));
        assert!(r.is_err(), "{v:?}: other program accepted in-circuit");
        // the code table's preprocessed opening tampered with
        let mut bad = proof.clone();
        let t = bad.batch_constraint_proof.column_openings.iter().position(|p| p.len() > 1).unwrap();
        bad.batch_constraint_proof.column_openings[t][1][0] += EF::ONE;
        assert!(!prog(&vk, &bad).is_empty());
        println!("NV_PREP_DEMO_REJECTED {v:?} other program, tampered code opening");
    }
}

/// `ToyBase` with an edited code table.
struct ToyBaseOther {
    base: ToyBase,
    edit: fn(&mut Vec<[u32; REC]>),
}
impl TestFixture<Sha384Config> for ToyBaseOther {
    fn airs(&self) -> Vec<AirRef<Sha384Config>> {
        let mut code = self.base.code();
        (self.edit)(&mut code);
        match self.base.v {
            Variant::Split => vec![Arc::new(ExecAir), Arc::new(CodeAir { code, rows: self.base.code_rows() }), Arc::new(RangeAir)],
            Variant::Fixed => vec![Arc::new(ExecAir), Arc::new(FixedAir { code })],
            Variant::Public => unreachable!(),
        }
    }
    fn generate_proving_ctx(&self) -> ProvingContext<CpuColMajorBackend<Sha384Config>> {
        // EXEC must fetch the edited records: rebuild its trace from the edited code
        let mut ctx = self.base.generate_proving_ctx();
        let mut code = self.base.code();
        (self.edit)(&mut code);
        let bytes = self.base.bytes();
        let mut v = vec![F::ZERO; self.base.exec_rows * E_W];
        let mut acc = F::ZERO;
        for i in 0..self.base.steps {
            let r = &mut v[i * E_W..(i + 1) * E_W];
            r[E_REAL] = F::ONE;
            for k in 0..REC {
                r[E_REC + k] = F::from_u32(code[i][k]);
            }
            r[E_BYTE] = F::from_u32(bytes[i]);
            r[E_ACC] = acc;
            acc += F::from_u32(code[i][4]) + F::from_u32(bytes[i]);
        }
        ctx.per_trace[0].1 = ctx_of(RowMajorMatrix::new(v, E_W), vec![acc]);
        ctx
    }
}
fn ctx_of(m: RowMajorMatrix<F>, pv: Vec<F>) -> AirProvingContext<CpuColMajorBackend<Sha384Config>> {
    ctx(m, pv)
}

fn nv_debug_nofail(vk: &openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<Sha384Config>, proof: &openvm_stark_backend::proof::Proof<Sha384Config>, log_rows: usize) {
    use openvm_cpu_backend::CpuBackend;
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

fn bincode_len(p: &openvm_stark_backend::proof::Proof<Sha384Config>) -> usize {
    use openvm_stark_backend::codec::Encode;
    let mut v = vec![];
    p.encode(&mut v).unwrap();
    v.len()
}

