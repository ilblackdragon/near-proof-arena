//! [agg] n-to-1 aggregation node on NV (lane/pq-base-aggregation, DESIGN-BASE.md §5).
//!
//! One NV proof verifies k >= 2 child proofs.  Each child's verifier runs on its own
//! transcript: the builder restarts the sponge between children (`Builder::restart_transcript`),
//! the hash-chain role starts a new chain there (input state = the initial-state constant), and
//! the ALU declares every chain start by anchoring the chain's first job with P3 = 1, so the
//! number and position of chain starts are fixed by the (bound) program.
//!
//! Statement: every node exposes NvAir public values [level, D] with
//!   D = SHA-384(prefix, tag 9, [n_ctx, n_state, ctx.., a, e, s_a.., s_e..])   (truncated like
//!   Merkle digests: 42 B under the lever),
//! "segments [a, e) of the chunk named by ctx take boundary state s_a to s_e".
//! * App children (level-1 node): child j's public values are [ctx.., j, pre.., post..].
//! * NV children (level >= 2): child i exposes [level, D_i]; the node witnesses the preimage
//!   of D_i, hashes it in-circuit and compares it with D_i.
//! The node checks ctx_i = ctx_0, a_{i+1} = e_i, s_a(i+1) = s_e(i) (continuity), then exposes
//! D(ctx, a_0, e_{k-1}, s_a(0), s_e(k-1)).  Above the tree root the digest passes through
//! unchanged (statement passthrough); V_d compares it with D(ctx, 0, S, S_0, S_S) computed
//! from the claimed chunk statement.
//!
//! Prototype limits (stated in results/pq-base-aggregation/README.md): program binding of NV
//! children is not emitted by this node (one BIND region per child is needed, §5.3 of the
//! design); levels of NV children must be equal (balanced tree).
use std::sync::Arc;

use openvm_stark_backend::{keygen::types::MultiStarkVerifyingKey, proof::Proof};
use p3_field::{PrimeCharacteristicRing, PrimeField32};

use super::{
    builder::{coeffs, ef_from, Builder, DigestCells, V},
    fmt::limbs_digest,
    verifier::build_verifier,
};
use crate::sha384::config::{range_digest, range_values, Digest, Sha384Config, F, TAG_RANGE};

/// A segment-range statement (native).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RangeStmt {
    pub ctx: Vec<F>,
    pub a: F,
    pub e: F,
    pub s_a: Vec<F>,
    pub s_e: Vec<F>,
}
impl RangeStmt {
    pub fn digest(&self) -> Digest {
        range_digest(&self.ctx, self.a, self.e, &self.s_a, &self.s_e)
    }
    pub fn values(&self) -> Vec<F> {
        range_values(&self.ctx, self.a, self.e, &self.s_a, &self.s_e)
    }
    /// The statement of one app segment from its public values [ctx.., j, pre.., post..].
    pub fn of_segment(pv: &[F], n_ctx: usize, n_state: usize) -> Self {
        assert_eq!(pv.len(), n_ctx + 1 + 2 * n_state, "segment public values");
        let j = pv[n_ctx];
        RangeStmt {
            ctx: pv[..n_ctx].to_vec(),
            a: j,
            e: j + F::ONE,
            s_a: pv[n_ctx + 1..n_ctx + 1 + n_state].to_vec(),
            s_e: pv[n_ctx + 1 + n_state..].to_vec(),
        }
    }
    /// Native composition (what an honest node exposes); None if the children do not chain.
    pub fn compose(children: &[RangeStmt]) -> Option<RangeStmt> {
        let f = children.first()?;
        for w in children.windows(2) {
            if w[1].ctx != f.ctx || w[1].a != w[0].e || w[1].s_a != w[0].s_e {
                return None;
            }
        }
        let l = children.last().unwrap();
        Some(RangeStmt { ctx: f.ctx.clone(), a: f.a, e: l.e, s_a: f.s_a.clone(), s_e: l.s_e.clone() })
    }
}

/// Native statement check of a node / final proof: public values 1..19 = D(stmt).
pub fn check_range_statement(nv_public_values: &[F], stmt: &RangeStmt) -> bool {
    let (lo, hi) = super::builder::digest_cells(stmt.digest());
    nv_public_values.len() == super::uair::NV_NUM_PVS && nv_public_values[1..13] == lo[..] && nv_public_values[13..19] == hi[..6]
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChildKind {
    /// app segment proofs (AIR 0 public values = [ctx.., j, pre.., post..])
    App { n_ctx: usize, n_state: usize },
    /// NV proofs exposing [level, D]; the node is given the preimages of the D's
    Node { n_ctx: usize, n_state: usize },
}

/// Statement cells.
struct StmtCells {
    ctx: Vec<V>,
    a: V,
    e: V,
    s_a: Vec<V>,
    s_e: Vec<V>,
}

/// In-circuit SHA-384 (tag 9) of the range message of `s`; returns the digest cells.
fn hash_range(b: &mut Builder, s: &StmtCells) -> DigestCells {
    let n_ctx = b.c(F::from_usize(s.ctx.len()));
    let n_state = b.c(F::from_usize(s.s_a.len()));
    let mut cells = vec![n_ctx, n_state];
    cells.extend(&s.ctx);
    cells.push(s.a);
    cells.push(s.e);
    cells.extend(&s.s_a);
    cells.extend(&s.s_e);
    let vals: Vec<F> = cells.iter().map(|c| coeffs(c.val)[0]).collect();
    let job = b.job_start(TAG_RANGE, 4 * cells.len());
    for (i, &x) in cells.iter().enumerate() {
        b.unit1(x, job, 2 + i as u32);
    }
    let d = crate::sha384::config::digest_from_bytes(crate::sha384::config::truncate_digest(
        crate::sha384::config::hash_parts(TAG_RANGE, &[&crate::sha384::config::felt_bytes(&vals)]),
    ));
    b.dig(job, d)
}

/// Pack 12 (or 6) base cells into one Ext12 cell: sum_k x_k X^k (basis cells cached).
fn pack(b: &mut Builder, basis: &mut Vec<V>, cells: &[V]) -> V {
    if basis.is_empty() {
        for k in 0..12 {
            let mut c = [F::ZERO; 12];
            c[k] = F::ONE;
            let v = b.ce(ef_from(c));
            basis.push(v);
        }
    }
    let mut acc = b.c(F::ZERO);
    for (k, &x) in cells.iter().enumerate() {
        let t = b.mul(x, basis[k]);
        acc = b.add(acc, t);
    }
    acc
}

/// The k-child aggregation program.  `preimages[i]` is child i's statement (used as witness
/// for NV children; ignored for app children).  Returns the exposed statement (native) as the
/// program computed it (also on failure, for diagnostics).
pub fn build_agg(
    b: &mut Builder,
    children: &[(&MultiStarkVerifyingKey<Sha384Config>, &Proof<Sha384Config>)],
    kind: ChildKind,
    preimages: &[RangeStmt],
) -> RangeStmt {
    assert!(children.len() >= 2, "an aggregation node has k >= 2 children");
    b.agg = true;
    let mut stmts: Vec<StmtCells> = vec![];
    let mut levels: Vec<V> = vec![];
    let mut basis: Vec<V> = vec![];
    for (i, &(vk, proof)) in children.iter().enumerate() {
        if i > 0 {
            b.restart_transcript();
        }
        // Level >= 2 child: bind its program to this node's (DESIGN-BASE §5.1).  Level-1 children
        // are base/app proofs, which have no NV program to bind.
        b.bind_child = matches!(kind, ChildKind::Node { .. });
        let pv = build_verifier(b, vk, proof);
        b.bind_child = false;
        match kind {
            ChildKind::App { n_ctx, n_state } => {
                let v = &pv[0];
                assert_eq!(v.len(), n_ctx + 1 + 2 * n_state, "segment public values");
                let a = v[n_ctx];
                let one = b.c(F::ONE);
                let e = b.add(a, one);
                stmts.push(StmtCells {
                    ctx: v[..n_ctx].to_vec(),
                    a,
                    e,
                    s_a: v[n_ctx + 1..n_ctx + 1 + n_state].to_vec(),
                    s_e: v[n_ctx + 1 + n_state..].to_vec(),
                });
            }
            ChildKind::Node { n_ctx, n_state } => {
                let v = &pv[0];
                assert_eq!(v.len(), super::uair::NV_NUM_PVS, "NV child public values");
                levels.push(v[0]);
                let w = &preimages[i];
                assert_eq!((w.ctx.len(), w.s_a.len()), (n_ctx, n_state));
                let mut ld = |b: &mut Builder, xs: &[F]| -> Vec<V> { xs.iter().map(|&x| b.load_f(x)).collect() };
                let s = StmtCells {
                    ctx: ld(b, &w.ctx),
                    a: b.load_f(w.a),
                    e: b.load_f(w.e),
                    s_a: ld(b, &w.s_a),
                    s_e: ld(b, &w.s_e),
                };
                // the preimage hashes to the child's exposed digest
                let dc = hash_range(b, &s);
                let lo = pack(b, &mut basis, &v[1..13]);
                let hi = pack(b, &mut basis, &v[13..19]);
                let limbs: Vec<F> = v[1..19].iter().map(|c| coeffs(c.val)[0]).collect();
                if limbs_digest(&limbs) != dc.digest {
                    b.failures.push(format!("child {i}: statement preimage"));
                }
                b.assert_eq(dc.lo, lo, "child statement digest lo");
                b.assert_eq(dc.hi, hi, "child statement digest hi");
                stmts.push(s);
            }
        }
    }
    // continuity: same chunk, adjacent ranges, boundary states equal
    for i in 1..stmts.len() {
        for (x, y) in stmts[i].ctx.clone().into_iter().zip(stmts[0].ctx.clone()) {
            b.assert_eq(x, y, &format!("child {i}: chunk context"));
        }
        let (a1, e0) = (stmts[i].a, stmts[i - 1].e);
        b.assert_eq(a1, e0, &format!("child {i}: segment index continuity"));
        for (x, y) in stmts[i].s_a.clone().into_iter().zip(stmts[i - 1].s_e.clone()) {
            b.assert_eq(x, y, &format!("child {i}: boundary state continuity"));
        }
    }
    // level: 1 over app proofs, else child level + 1 (all children at the same level)
    let level = match kind {
        ChildKind::App { .. } => b.c(F::ONE),
        ChildKind::Node { .. } => {
            for i in 1..levels.len() {
                b.assert_eq(levels[i], levels[0], "children at the same level");
            }
            let one = b.c(F::ONE);
            b.add(levels[0], one)
        }
    };
    b.pv_level(level);
    let (f, l) = (&stmts[0], &stmts[stmts.len() - 1]);
    let out = StmtCells { ctx: f.ctx.clone(), a: f.a, e: l.e, s_a: f.s_a.clone(), s_e: l.s_e.clone() };
    let dc = hash_range(b, &out);
    b.pv_digest(&dc);
    let val = |c: &V| coeffs(c.val)[0];
    RangeStmt {
        ctx: out.ctx.iter().map(val).collect(),
        a: val(&out.a),
        e: val(&out.e),
        s_a: out.s_a.iter().map(val).collect(),
        s_e: out.s_e.iter().map(val).collect(),
    }
}

// ---------------------------------------------------------------------------------------
// Design G level 1: one main (shared-transcript) base proof + linked sub-proofs (P-PERF-8 PREP /
// code-hash proofs).  No segment statements: continuity is inside the main proof.
// ---------------------------------------------------------------------------------------

/// A cross-proof link: public value `sub_pv` of AIR 0 of child `sub` must equal public value
/// `main_pv` of AIR 0 of the main child (child 0), e.g. "PREP proof's code-table commitment = the
/// commitment the main proof's FETCH table uses".
#[derive(Clone, Copy, Debug)]
pub struct Link {
    pub sub: usize,
    pub sub_pv: usize,
    pub main_pv: usize,
}

/// L1 of design G: verify child 0 (the main base proof) and children 1.. (sub-proofs, any vks), each on
/// its own transcript; check the links; expose level 1 and the tag-8 statement digest of the main
/// proof's public values (the recursion lane's G1 format, so T1.. pass it through unchanged).
pub fn build_l1_linked(
    b: &mut Builder,
    children: &[(&MultiStarkVerifyingKey<Sha384Config>, &Proof<Sha384Config>)],
    links: &[Link],
) -> Digest {
    b.agg = true;
    let mut pvs: Vec<Vec<Vec<V>>> = vec![];
    for (i, &(vk, proof)) in children.iter().enumerate() {
        if i > 0 {
            b.restart_transcript();
        }
        pvs.push(build_verifier(b, vk, proof));
    }
    for (n, l) in links.iter().enumerate() {
        assert!(l.sub >= 1 && l.sub < children.len());
        let (x, y) = (pvs[l.sub][0][l.sub_pv], pvs[0][0][l.main_pv]);
        b.assert_eq(x, y, &format!("link {n}: sub-proof {} pv {} = main pv {}", l.sub, l.sub_pv, l.main_pv));
    }
    let one = b.c(F::ONE);
    b.pv_level(one);
    let main = &pvs[0];
    let mut cells: Vec<V> = vec![b.c(F::from_usize(main.len()))];
    for p in main {
        let n = b.c(F::from_usize(p.len()));
        cells.push(n);
    }
    cells.extend(main.iter().flatten().copied());
    let job = b.job_start(crate::sha384::config::TAG_STATEMENT, 4 * cells.len());
    for (i, &x) in cells.iter().enumerate() {
        b.unit1(x, job, 2 + i as u32);
    }
    let d = crate::sha384::config::statement_digest(&children[0].1.public_values);
    let dc = b.dig(job, d);
    b.pv_digest(&dc);
    d
}

/// Native check of the G statement: public values 1..19 = tag-8 digest of the main proof's values.
pub fn check_statement(nv_public_values: &[F], main_public_values: &[Vec<F>]) -> bool {
    let (lo, hi) = super::builder::digest_cells(crate::sha384::config::statement_digest(main_public_values));
    nv_public_values.len() == super::uair::NV_NUM_PVS && nv_public_values[1..13] == lo[..] && nv_public_values[13..19] == hi[..6]
}

// ---------------------------------------------------------------------------------------
// Segment fixture: a Fibonacci machine split into segments (state (l, r), r' = l + r)
// ---------------------------------------------------------------------------------------

/// Segment AIR: columns (l, r); public values [ctx.. (n_ctx), j, pre_l, pre_r, post_l, post_r];
/// first row = pre, transition (l, r) -> (r, l + r), post = step(last row).
#[derive(Clone, Copy)]
pub struct SegAir {
    pub n_ctx: usize,
}
impl<T> p3_air::BaseAir<T> for SegAir {
    fn width(&self) -> usize {
        2
    }
}
impl<T> openvm_stark_backend::BaseAirWithPublicValues<T> for SegAir {
    fn num_public_values(&self) -> usize {
        self.n_ctx + 5
    }
}
impl<T> openvm_stark_backend::PartitionedBaseAir<T> for SegAir {}
impl<AB: p3_air::AirBuilderWithPublicValues> p3_air::Air<AB> for SegAir {
    fn eval(&self, builder: &mut AB) {
        use p3_air::AirBuilder;
        use p3_matrix::Matrix;
        let main = builder.main();
        let pv: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let (lc, nc) = (main.row_slice(0).unwrap(), main.row_slice(1).unwrap());
        let (l, r): (AB::Expr, AB::Expr) = (lc[0].clone().into(), lc[1].clone().into());
        let (nl, nr): (AB::Expr, AB::Expr) = (nc[0].clone().into(), nc[1].clone().into());
        let o = self.n_ctx + 1;
        builder.when_first_row().assert_eq(l.clone(), pv[o].clone());
        builder.when_first_row().assert_eq(r.clone(), pv[o + 1].clone());
        builder.when_transition().assert_eq(nl, r.clone());
        builder.when_transition().assert_eq(nr, l.clone() + r.clone());
        // post = the state after the last row (the next segment's first row)
        builder.when_last_row().assert_eq(r.clone(), pv[o + 2].clone());
        builder.when_last_row().assert_eq(l + r, pv[o + 3].clone());
    }
}

#[cfg(any(test, feature = "test-utils"))]
/// Segment j of a chunk: n rows from state `pre`.
#[derive(Clone, Debug)]
pub struct SegFixture {
    pub ctx: Vec<F>,
    pub j: u64,
    pub pre: (F, F),
    pub n: usize,
}
#[cfg(any(test, feature = "test-utils"))]
impl SegFixture {
    pub fn rows(&self) -> Vec<(F, F)> {
        let mut v = vec![self.pre];
        for _ in 1..self.n {
            let (l, r) = *v.last().unwrap();
            v.push((r, l + r));
        }
        v
    }
    /// State after the segment (the next segment's pre-state).
    pub fn post(&self) -> (F, F) {
        let (l, r) = *self.rows().last().unwrap();
        (r, l + r)
    }
    pub fn public_values(&self) -> Vec<F> {
        let p = self.post();
        let mut v = self.ctx.clone();
        v.extend([F::from_u64(self.j), self.pre.0, self.pre.1, p.0, p.1]);
        v
    }
    pub fn stmt(&self) -> RangeStmt {
        RangeStmt::of_segment(&self.public_values(), self.ctx.len(), 2)
    }
    /// The next segment (continuing from this one's post-state).
    pub fn next(&self) -> SegFixture {
        let p = self.post();
        SegFixture { ctx: self.ctx.clone(), j: self.j + 1, pre: p, n: self.n }
    }
}
#[cfg(any(test, feature = "test-utils"))]
impl openvm_stark_backend::test_utils::TestFixture<Sha384Config> for SegFixture {
    fn airs(&self) -> Vec<openvm_stark_backend::AirRef<Sha384Config>> {
        vec![Arc::new(SegAir { n_ctx: self.ctx.len() })]
    }
    fn generate_proving_ctx(
        &self,
    ) -> openvm_stark_backend::prover::ProvingContext<openvm_stark_backend::prover::CpuColMajorBackend<Sha384Config>> {
        use openvm_stark_backend::prover::{AirProvingContext, ColMajorMatrix, ProvingContext};
        let v: Vec<F> = self.rows().into_iter().flat_map(|(l, r)| [l, r]).collect();
        let m = p3_matrix::dense::RowMajorMatrix::new(v, 2);
        ProvingContext::new(vec![(0, AirProvingContext::simple(ColMajorMatrix::from_row_major(&m), self.public_values()))])
    }
}

/// A chunk of `s` consecutive segments of `n` rows each.
#[cfg(any(test, feature = "test-utils"))]
pub fn chunk_segments(ctx: &[u64], s: usize, n: usize) -> Vec<SegFixture> {
    let mut v = vec![SegFixture { ctx: ctx.iter().map(|&x| F::from_u64(x)).collect(), j: 0, pre: (F::ZERO, F::ONE), n }];
    while v.len() < s {
        let nx = v.last().unwrap().next();
        v.push(nx);
    }
    v
}

#[cfg(any(test, feature = "test-utils"))]
#[allow(dead_code)]
fn _unused(x: F) -> u32 {
    x.as_canonical_u32()
}
