import ZkFormal.PQ.NvSha

/-!
# ZkFormal.PQ.NvNode — `NodeSha` and `NodeLink` from the circuit, and `NodeExecV` from named premises

Lane E (E2E M11i, item 1), 2026-11-21. With the statement digest `rdig pre st` (the native
`RangeStmt::digest` of `agg.rs`, as digest cells: `NvShaNative.rangeLimbs` of
`stmtVals st` = `[n_ctx, n_state, ctx.., a, e, s_a.., s_e..]`) and boundary vectors as raw cells
(`enc = id`), this file proves the two components of M11g's `nodeExecV_of_prog` that were open:

* **`nodeSha_of`** (`E2ENode.NodeSha`): every `hash_range` job of the node — one per node child
  and `out` — laid out as `build_agg` emits it has `Dig` cells equal to `rdig pre` of the
  statement its unit cells denote (`NvSha.range_cells` + `vals_of`: the two length cells are
  `Const` rows, the others the read's cells).
* **`nodeLink_app`** (app children, `of_segment`): the statement cells are the child's public
  value cells, and `e = a + 1` is the program's `Add` of `a` and the constant `1` (`add_sem`,
  `const_sem`). **`nodeLink_node`** (node children): the child digest cells are asserted equal to
  the packed public-value cells (`asserted_eq`); that the packed cells hold the public values
  (`PackOK`: `pack`'s `Mul`-by-basis / `Add` chain, and the verifier's public-value cells being
  base-field) is a **named premise** (the Ext12 multiplication semantics of the ALU is not
  partially evaluated here).
* **`nodeExecV_of_contracts`**: `NodeExecV` (the node's execution obligation over `NvHold`) from
  program binding of the whole column (`ProgFull`), `GlueByteBool`, the SHA contract
  (`ShaContract`), the range-digest tail pin (`TailCanon`, the circuit gap found in `NvSha`),
  `PackOK` (node children only), the inner-verifier acceptance (`NodeInner`, the extractor's
  output) and the program's layout facts.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace ZkFormal.PQ.NvNode

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.NvTape ZkFormal.PQ.NvField ZkFormal.PQ.NvProg
open ZkFormal.PQ.NvOps ZkFormal.PQ.NvShaNative ZkFormal.PQ.NvSha
open ZkFormal.PQ.E2ENode ZkFormal.PQ.E2EHold
open ZkFormal.PQ.Aggregation.Stmt

/-! ## The native statement digest -/

/-- `range_values` of a statement: `[n_ctx, n_state, ctx.., a, e, s_a.., s_e..]`. -/
def stmtVals (st : Stmt (List Fp)) : List Fp :=
  [((st.ctx.length : Nat) : Fp), ((st.sa.length : Nat) : Fp)] ++ st.ctx ++
    [((st.a : Nat) : Fp), ((st.e : Nat) : Fp)] ++ st.sa ++ st.se

/-- **The native range digest as digest cells** (`range_digest` → `digest_cells`). -/
def rdig (pre : Bytes) (st : Stmt (List Fp)) : List Fp := rangeLimbs pre (stmtVals st)

/-- The 18 digest cells a job's two `Dig` rows hold. -/
def digOf (tr : Trace Fp) (J : RangeJob) : List Fp := cellOf tr J.dlo ++ (cellOf tr J.dhi).take 6

/-- A statement cell's values in message order. -/
def cellVals (c : SCell) : List Fp := c.ctx ++ [c.a, c.e] ++ c.sa ++ c.se

theorem cast_toNat (x : Fp) : ((x.toNat : Nat) : Fp) = x := Fp.ofNat_toNat x

theorem stmtVals_cell (c : SCell) :
    stmtVals (c.stmt id) = [((c.ctx.length : Nat) : Fp), ((c.sa.length : Nat) : Fp)] ++ cellVals c := by
  simp [stmtVals, SCell.stmt, cellVals, cast_toNat]

/-- The unit cells of a `hash_range` job: two `Const` rows holding the lengths, then cells whose
values are the statement cell's (a read-layout fact). -/
def JobCells (tr : Trace Fp) (prog : List Instr) (J : RangeJob) (c : SCell) : Prop :=
  ∃ cN cS addrs, J.cs = cN :: cS :: addrs ∧
    (∃ h : cN < prog.length, prog[cN] = ⟨4, c.ctx.length, 0, 0, 0⟩) ∧
    (∃ h : cS < prog.length, prog[cS] = ⟨4, c.sa.length, 0, 0, 0⟩) ∧
    addrs.map (fun a => cv tr 0 a 46) = cellVals c

section Sha

variable {tr : Trace Fp} {pub : List Fp} {prog : List Instr}

theorem vals_of (hh : NvHold pub tr) (hG : GlueByteBool tr pub) (hP : ProgBound tr prog)
    (hW : ProgWF prog) {J : RangeJob} {c : SCell} (hc : JobCells tr prog J c) :
    J.vals tr = stmtVals (c.stmt id) := by
  obtain ⟨cN, cS, addrs, hcs, ⟨hN, hNi⟩, ⟨hS, hSi⟩, ha⟩ := hc
  rw [stmtVals_cell, RangeJob.vals, hcs, List.map_cons, List.map_cons, ha,
    (const_sem hh hG hP hW hN hNi).1, (const_sem hh hG hP hW hS hSi).1]
  rfl

/-- **One `hash_range` job's digest cells are the native digest of its statement.** -/
theorem job_dig (pre : Bytes) (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    (hP : ProgFull tr prog) (hW : ProgWF prog) (hC : ShaContract pre tr pub) {J : RangeJob}
    (hJ : J.OK prog) (hT : TailCanon tr J.dhi) {c : SCell} (hc : JobCells tr prog J c) :
    digOf tr J = rdig pre (c.stmt id) := by
  rw [digOf, range_cells pre hh hG hP hW hC hJ hT, vals_of hh hG hP.1 hW hc]
  rfl

/-- **`NodeSha` from the SHA contract**, for a read whose digests are its jobs' `Dig` cells and
whose statement cells are the jobs' unit cells. -/
theorem nodeSha_of (pre : Bytes) (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    (hP : ProgFull tr prog) (hW : ProgWF prog) (hC : ShaContract pre tr pub)
    {K : NodeKey} {Proof : Type} (R : NodeRead K (List Fp) Proof)
    (kid : Fin K.k → RangeJob) (out : RangeJob)
    (hk : K.kind = .node → ∀ i, (kid i).OK prog ∧ TailCanon tr (kid i).dhi ∧
      JobCells tr prog (kid i) (R.cell i) ∧ R.kidDig i = digOf tr (kid i))
    (ho : out.OK prog ∧ TailCanon tr out.dhi ∧ JobCells tr prog out (outCell R.cells) ∧
      R.outDig = digOf tr out) :
    NodeSha id (rdig pre) R := by
  refine ⟨fun hn i => ?_, ?_⟩
  · obtain ⟨hJ, hT, hc, hd⟩ := hk hn i
    rw [hd, job_dig pre hh hG hP hW hC hJ hT hc]
  · obtain ⟨hJ, hT, hc, hd⟩ := ho
    rw [hd, job_dig pre hh hG hP hW hC hJ hT hc]

end Sha

/-! ## `NodeLink` -/

/-- `RangeStmt::of_segment` on public values `[ctx.., j, pre.., post..]`, as a statement cell. -/
def segCell (nCtx nState : Nat) (pv : List Fp) : SCell :=
  ⟨pv.take nCtx, pv.getD nCtx 0, pv.getD nCtx 0 + 1, (pv.drop (nCtx + 1)).take nState,
    pv.drop (nCtx + 1 + nState)⟩

/-- The segment statement of public values (the `segStmt` of the app node). -/
def segStmtC (nCtx nState : Nat) (pv : List Fp) : Stmt (List Fp) := (segCell nCtx nState pv).stmt id

/-- The child-digest part of node public values `[level, D..]`. -/
def pvDigC (pv : List Fp) : List Fp := (pv.drop 1).take 18

section Link

variable {tr : Trace Fp} {pub : List Fp} {prog : List Instr}

/-- **`NodeLink` for app children.** The statement cells are the child's public-value cells
(`build_agg` slices `pv`), except `e`, which the program computes as `Add(a, Const 1)`. -/
theorem nodeLink_app (hh : NvHold pub tr) (hG : GlueByteBool tr pub) (hP : ProgBound tr prog)
    (hW : ProgWF prog) {K : NodeKey} {Proof : Type} (R : NodeRead K (List Fp) Proof)
    (hkind : K.kind = .app)
    (aAddr eRow one : Fin K.k → Nat)
    (hread : ∀ i, List.ofFn (R.ctx i) = (R.pv i).take K.nCtx ∧ R.a i = (R.pv i).getD K.nCtx 0 ∧
      R.a i = cv tr 0 (aAddr i) 46 ∧ R.e i = cv tr 0 (eRow i) 46 ∧
      List.ofFn (R.sa i) = ((R.pv i).drop (K.nCtx + 1)).take K.nState ∧
      List.ofFn (R.se i) = (R.pv i).drop (K.nCtx + 1 + K.nState))
    (hprog : ∀ i, ∃ (he : eRow i < prog.length) (ho : one i < prog.length),
      prog[eRow i] = ⟨2, aAddr i, one i, 0, 0⟩ ∧ prog[one i] = ⟨4, 1, 0, 0, 0⟩ ∧
      aAddr i < 2 ^ 24 ∧ one i < 2 ^ 24)
    (pvDig : List Fp → List Fp) : NodeLink id pvDig (segStmtC K.nCtx K.nState) R := by
  unfold NodeLink
  rw [hkind]
  intro i
  obtain ⟨hc, ha, ha', he, hs, hse⟩ := hread i
  obtain ⟨heL, hoL, hei, hoi, hal, hol⟩ := hprog i
  have hadd := add_sem hh hG hP hW heL hei hal hol 0 (by decide)
  have h1 := (const_sem hh hG hP hW hoL hoi).1
  have hE : R.e i = (R.pv i).getD K.nCtx 0 + 1 := by
    rw [he, hadd, ← ha', ha, h1]; rfl
  show (R.cell i).stmt id = (segCell K.nCtx K.nState (R.pv i)).stmt id
  congr 1
  simp only [NodeRead.cell, segCell, hc, ha, hE, hs, hse]

/-- **Premise (ALU arithmetic, node children)**: the packed cells hold the child's public values
(`agg.rs::pack`: `Σ_k pv_k·X^k` over base-field public-value cells). -/
def PackOK (tr : Trace Fp) (plo phi : Nat) (pv : List Fp) : Prop :=
  cellOf tr plo = (pv.drop 1).take 12 ∧ (cellOf tr phi).take 6 = (pv.drop 13).take 6

theorem cellOf_congr {x y : Nat} (h : CellEq tr x y) : cellOf tr x = cellOf tr y := by
  unfold cellOf
  apply List.map_congr_left
  intro k hk
  exact h k (List.mem_range.1 hk)

/-- **`NodeLink` for node children**: the program asserts the child digest cells equal to the
packed public-value cells (`assert_eq(dc.lo, lo)`, `assert_eq(dc.hi, hi)`). -/
theorem nodeLink_node {K : NodeKey} {Proof : Type} (R : NodeRead K (List Fp) Proof)
    (hkind : K.kind = .node) (kid : Fin K.k → RangeJob) (plo phi : Fin K.k → Nat)
    (hd : ∀ i, R.kidDig i = digOf tr (kid i))
    (hEq : ∀ i, CellEq tr (kid i).dlo (plo i) ∧ CellEq tr (kid i).dhi (phi i))
    (hpack : ∀ i, PackOK tr (plo i) (phi i) (R.pv i))
    (segStmt : List Fp → Stmt (List Fp)) : NodeLink id pvDigC segStmt R := by
  unfold NodeLink
  rw [hkind]
  intro i
  obtain ⟨e1, e2⟩ := hEq i
  obtain ⟨p1, p2⟩ := hpack i
  rw [hd i, digOf, cellOf_congr e1, cellOf_congr e2, p1, p2, pvDigC]
  rw [show (R.pv i).drop 13 = ((R.pv i).drop 1).drop 12 by rw [List.drop_drop],
    show (18 : Nat) = 12 + 6 from rfl, List.take_add]

end Link

/-! ## `NodeExecV` from the named premises -/

section Exec

variable {K : NodeKey} {Proof : Type} (pre : Bytes) (InnerAcc : Proof → List Fp → Prop)
  (pvDig : List Fp → List Fp) (segStmt : List Fp → Stmt (List Fp))

/-- **The node's execution obligation over `NvHold`, from the named premises.** Proved
components: the tape (`PvD`), the continuity asserts (M11g), SHA (`nodeSha_of`), the links
(through `hLink`, discharged by `nodeLink_app` / `nodeLink_node`). Premises: program binding of the
whole column (`ProgFull`), `GlueByteBool`, the SHA contract (`ShaContract`), the range-digest tail
pin (`TailCanon`, a circuit gap), the inner-verifier acceptance (`NodeInner`: the extractor), and
the program's layout facts (`RangeJob.OK`, `JobCells`, `NodeLay`, `ContProg`, the `PvD` rows),
which are decidable on the pinned program. -/
theorem nodeExecV_of_contracts (R : Trace Fp → NodeRead K (List Fp) Proof)
    (prog : List Instr) (hW : ProgWF prog) (L : NodeLay K)
    (kid : Fin K.k → RangeJob) (out : RangeJob)
    (hlo : out.dlo < prog.length) (hhi : out.dhi < prog.length)
    {alo ahi : Nat} (hilo : prog[out.dlo]'hlo = ⟨31, alo, 0, 0, 0⟩)
    (hihi : prog[out.dhi]'hhi = ⟨31, ahi, 0, 1, 0⟩) (halo : alo < 2 ^ 24) (hahi : ahi < 2 ^ 24)
    (hCont : ContProg prog L)
    (hP : ∀ tr pub, NvHold pub tr → ProgFull tr prog)
    (hG : ∀ tr pub, NvHold pub tr → GlueByteBool tr pub)
    (hC : ∀ tr pub, NvHold pub tr → ShaContract pre tr pub)
    (hT : ∀ tr pub, NvHold pub tr → TailCanon tr out.dhi ∧
      (K.kind = .node → ∀ i, TailCanon tr (kid i).dhi))
    (hJ : out.OK prog ∧ (K.kind = .node → ∀ i, (kid i).OK prog))
    (hcells : ∀ tr, JobCells tr prog out (outCell (R tr).cells) ∧
      (K.kind = .node → ∀ i, JobCells tr prog (kid i) ((R tr).cell i)))
    (hRd : ∀ tr, (R tr).outDig = digCells tr 0 alo ahi ∧ (R tr).outDig = digOf tr out ∧
      ReadsLay tr L (R tr) ∧ (K.kind = .node → ∀ i, (R tr).kidDig i = digOf tr (kid i)))
    (hLink : ∀ tr pub, NvHold pub tr → (∀ x y, AssertIn prog x y → CellEq tr x y) →
      NodeLink id pvDig segStmt (R tr))
    (hInner : ∀ tr pub, NvHold pub tr → NodeInner InnerAcc (R tr)) :
    NodeExecV id (rdig pre) InnerAcc pvDig segStmt R (fun p => pvDigest p) := by
  refine nodeExecV_of_prog id (rdig pre) InnerAcc pvDig segStmt R id prog hW L hlo hhi hilo hihi
    halo hahi hCont (fun tr pub hh => (hP tr pub hh).1) hG
    (fun tr => ⟨(hRd tr).1, (hRd tr).2.2.1⟩) hLink (fun tr pub hh => ⟨?_, hInner tr pub hh⟩)
  exact nodeSha_of pre hh (hG tr pub hh) (hP tr pub hh) hW (hC tr pub hh) (R tr) kid out
    (fun hn i => ⟨hJ.2 hn i, (hT tr pub hh).2 hn i, (hcells tr).2 hn i, (hRd tr).2.2.2 hn i⟩)
    ⟨hJ.1, (hT tr pub hh).1, (hcells tr).1, (hRd tr).2.1⟩

end Exec

#print axioms vals_of
#print axioms job_dig
#print axioms nodeSha_of
#print axioms nodeLink_app
#print axioms nodeLink_node
#print axioms nodeExecV_of_contracts

end ZkFormal.PQ.NvNode
