import ZkFormal.PQ.E2EAgg
import NearSpecV3.E2E.Boundary

/-!
# ZkFormal.PQ.E2ENode — `NvFaithful` for the aggregation node and wrap, down to the AIR execution

Lane E (E2E M11d), 2026-11-03. `E2EAgg.lean` (M11c) takes `NvFaithful` of the node circuit and of
the wrap circuit as hypotheses. Of `NvFaithful.lean`'s six sub-obligations, only LogUp (5) was
proved. This file transcribes the pinned node program, `build_agg` in
`research/near-compression/native/recursion/patches/openvm-recursion-agg.patch`, and the wrap
program of plan §3.4 into Lean *at the program level*. It then proves everything about them that
does not need a Lean model of the NvAir constraints.

## What `build_agg` does, cell by cell (`agg.rs`)

* `assert!(children.len() >= 2)`: the key has a fixed `k ≥ 2` children. `NodeKey.two_le`.
* Per child `i`, `build_verifier(b, vk, proof)` returns the child's public-value cells `pv_i`.
  The statement cells `StmtCells` are then:
  * for an app child, the slices `pv_i[..n_ctx]`, `pv_i[n_ctx]` and `pv_i[n_ctx] + 1`, followed by
    the two state slices (`of_segment`);
  * for a node child, `n_ctx + 2 + 2·n_state` loaded cells (`load_f`). Their tag-9 SHA-384 job
    `hash_range` is asserted equal to the child's exposed digest cells `pv_i[1..19]` (two packed
    `assert_eq`).

  In both cases every vector has the fixed length `n_ctx` or `n_state`: for app children a fixed
  slice, for node children the build-time `assert_eq!((w.ctx.len(), w.s_a.len()), (n_ctx, n_state))`.
  `NodeRead` builds the cells with `List.ofFn` over `Fin n_ctx` and `Fin n_state`.
* Continuity, `for i in 1..len`: `zip(ctx_i, ctx_0)`, `a_i = e_{i-1}`, `zip(s_a_i, s_e_{i-1})`, all
  `assert_eq`. `ContAsserts`, with `zipEq` the Rust `zip` loop.
* `out = (f.ctx, f.a, l.e, f.s_a, l.s_e)` (`outCell`). Its tag-9 job is exposed as the node's
  public digest (`pv_digest`).

## What is proved (standard axioms only)

* `zipEq_eq`: the `zip` loop proves list equality only because the lengths are equal.
  `zipEq_short` shows that without equal lengths it would accept different contexts. The fixed
  shape is therefore load-bearing.
* `compose_of_asserts`: the continuity asserts on shaped cells give
  `Stmt.compose (cells.map stmt) = some (stmt (outCell cells))`, i.e. the program computes the
  native `RangeStmt::compose`.
* `node_composition`: **sub-obligation 6 (composition) for the node.** On a read that satisfies
  the node's per-trace components (`NodeSha`, `NodeInner`, `NodeTape`, `NodeAsserts`), the native
  node program `aggNodeV` accepts the decoded statement and children. `nvFaithful_node` turns it
  into `NvFaithful Pin (nodeDecode R pubDig par) (aggNodeV Acc rdigest)` from `NodeExec`.
* `wrap_composition` and `nvFaithful_wrap`: the same for the wrap program `aggWrapV`.
* `nvComposition_node`: the node's composition *in the generic form* of `NvFaithful.lean`
  (`NvCompositionAt`, with its `HoldsLogUp` premise, amended in this milestone). Here
  `arithOK := NodeAsserts ∧ NodeInner`, the SHA slot carries the node's tag-9 jobs, and the tape
  slot carries `pubDig pub = outDig`.
* `leafHolds_circ`: **`LeafHolds` is discharged.** `circSeg` is the circuit's segment system: a
  segment instance is a template trace satisfying the template AIR (`Holds`, natural balance),
  whose public statement has the instance's boundaries. `LeafHolds` is a theorem for every
  aggregation interface over it, via `holds_of_holdsLogUp`.
* `rangeBinding_of`: **`RangeBinding` reduces to collision resistance.** The pinned range message
  `rmsg` (`range_values`: `[n_ctx, n_state, ctx.., a, e, s_a.., s_e..]`) is injective for any
  injective boundary encoding (`rmsg_inj`; the two length prefixes make it self-delimiting).
  `rdigest = H ∘ rmsg` is therefore binding unless `H` collides (`HColl H`). For
  `H = bdigest ∘ ser` with an injective `ser`, an `H` collision is a 42-byte SHA-384 collision
  (`hColl_bdigest`).

## What remains, and why it cannot be proved here

`NodeExec` / `WrapExec`: on every trace satisfying the pinned NvAir with the LogUp balance, the
program's cell values satisfy the four components. These are sub-obligations 1–4 of
`NvFaithful.lean` restricted to this program:

| component | what the AIR must enforce | generic # |
|---|---|---|
| `NodeSha` | each `hash_range` job's digest cells are the true tag-9 SHA-384 (42 B) of the message cells | 1 |
| `NodeInner` | each `build_verifier` gadget accepts child `i` natively with public values `pv_i`: T* challenges and verifier arithmetic | 2 + 4 (recursive: the inner verifier's own faithfulness) |
| `NodeTape` | the public-value cells are the `pv_digest` cells (statement passthrough); the program columns are the pinned `P_NV` | 3 |
| `NodeAsserts` | every `assert_eq` of the program holds on the cells: links and continuity | 4 |

All four are claims about the NvAir constraints (`crates/recursion/src/nv/*`: 74 columns, 49
interactions per row, plus `Sha512Air`, `TableAir` and `ByteAir`). No Lean value of that AIR exists:
`grep -rn NvAir --include=*.lean` finds only interface files, and no exporter emits the NV crate.
Each component is therefore a premise about an opaque `HoldsLogUp Pin.air`. They cannot be proved
or refuted here. They are generic to the NV circuit and do not depend on the node: the
program-specific part is proved above. The wrap is not built yet (plan §1.5: "a sibling agent is
building it for D0a"), so `WrapExec` is stated against the plan §3.4 design.

One prototype limit is recorded in `agg.rs`'s header: "program binding of NV children is not
emitted by this node". The code sets `b.bind_child = true` for node children, so the header comment
looks stale. If binding were absent, `NodeInner` would fail: a child proof under a different
program would pass. `NodeInner` must therefore be read as including program binding (`BIND`) of
node children.
-/

namespace ZkFormal.PQ.E2ENode

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.Nv ZkFormal.PQ.E2EBridge ZkFormal.PQ.E2EAgg
open ZkFormal.PQ.Aggregation.Stmt
open NearSpecV3.E2E

/-! ## Statement cells and the continuity asserts -/

/-- `StmtCells` of `agg.rs`: the cells of one range statement. -/
structure SCell where
  ctx : List Fp
  a : Fp
  e : Fp
  sa : List Fp
  se : List Fp

/-- The range statement the cells denote, with boundary vectors encoded by `enc`. -/
def SCell.stmt {α : Type} (enc : List Fp → α) (c : SCell) : Stmt α :=
  ⟨enc c.ctx, c.a.toNat, c.e.toNat, enc c.sa, enc c.se⟩

/-- The Rust loop `for (x, y) in xs.zip(ys) { b.assert_eq(x, y) }`. -/
def zipEq (xs ys : List Fp) : Prop := ∀ p ∈ xs.zip ys, p.1 = p.2

/-- The fixed shape of the cells (`n_ctx`, `n_state`). -/
def Shape (nCtx nState : Nat) (c : SCell) : Prop :=
  c.ctx.length = nCtx ∧ c.sa.length = nState ∧ c.se.length = nState

/-- The continuity loop of `build_agg` (`for i in 1..stmts.len()`), indexed from `0`. -/
def ContAsserts (ss : List SCell) : Prop :=
  ∀ i (h : i + 1 < ss.length),
    zipEq (ss[i + 1]).ctx (ss[0]'(by omega)).ctx ∧ (ss[i + 1]).a = (ss[i]'(by omega)).e ∧
      zipEq (ss[i + 1]).sa (ss[i]'(by omega)).se

/-- `out = (f.ctx, f.a, l.e, f.s_a, l.s_e)`. -/
def outCell : List SCell → SCell
  | [] => ⟨[], 0, 0, [], []⟩
  | f :: rest =>
    let l := rest.getLast?.getD f
    ⟨f.ctx, f.a, l.e, f.sa, l.se⟩

/-- **The `zip` loop proves equality of equal-length vectors.** -/
theorem zipEq_eq : ∀ {xs ys : List Fp}, xs.length = ys.length → zipEq xs ys → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, h, hz => by
    have hxy : x = y := hz (x, y) (by simp)
    have := zipEq_eq (xs := xs) (ys := ys) (by simpa using h)
      (fun p hp => hz p (by simp [hp]))
    rw [hxy, this]

/-- **Without equal lengths the `zip` loop is not equality**: it accepts a strict prefix. So the
fixed shape (`NodeKey.nCtx`, `NodeKey.nState`) is load-bearing. -/
theorem zipEq_short : zipEq [0] [0, 1] ∧ ([0] : List Fp) ≠ [0, 1] :=
  ⟨by intro p hp; simp at hp; subst hp; rfl, by simp⟩

/-- Adjacent statements that chain make a chainable list. -/
theorem chainable_of_adj {α : Type} :
    ∀ (l : List (Stmt α)), (∀ i (h : i + 1 < l.length), Chains (l[i]'(by omega)) l[i + 1]) →
      Chainable l
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: rest, h =>
    ⟨h 0 (by simp), chainable_of_adj (b :: rest) (fun i hi => h (i + 1) (by simp at hi ⊢; omega))⟩

theorem getD_map {β γ : Type} (g : β → γ) (o : Option β) (x : β) :
    (o.map g).getD (g x) = g (o.getD x) := by
  cases o <;> rfl

/-- **The continuity asserts compute `RangeStmt::compose`.** On cells of the fixed shape, the
asserts of `build_agg` make `compose` of the denoted statements succeed, and its value is the
statement of `outCell`. -/
theorem compose_of_asserts {α : Type} [DecidableEq α] (enc : List Fp → α) (nCtx nState : Nat)
    (ss : List SCell) (hne : ss ≠ []) (hsh : ∀ c ∈ ss, Shape nCtx nState c)
    (hc : ContAsserts ss) :
    compose (ss.map (SCell.stmt enc)) = some ((outCell ss).stmt enc) := by
  have hctx0 : ∀ i (h : i < ss.length), (ss[i]).ctx = (ss[0]'(by omega)).ctx := by
    intro i h
    cases i with
    | zero => rfl
    | succ j =>
      have h1 := (hsh _ (List.getElem_mem h)).1
      have h0 := (hsh _ (List.getElem_mem (show 0 < ss.length by omega))).1
      exact zipEq_eq (by rw [h1, h0]) (hc j h).1
  have hch : Chainable (ss.map (SCell.stmt enc)) := by
    apply chainable_of_adj
    intro i h
    simp only [List.length_map] at h
    simp only [List.getElem_map]
    refine ⟨?_, ?_, ?_⟩
    · show enc _ = enc _
      rw [hctx0 (i + 1) h, hctx0 i (by omega)]
    · show Fp.toNat _ = Fp.toNat _
      rw [(hc i h).2.1]
    · show enc _ = enc _
      have h1 := (hsh _ (List.getElem_mem h)).2.1
      have h2 := (hsh _ (List.getElem_mem (show i < ss.length by omega))).2.2
      rw [zipEq_eq (by rw [h1, h2]) (hc i h).2.2]
  cases ss with
  | nil => exact absurd rfl hne
  | cons f rest =>
    rw [List.map_cons] at hch ⊢
    rw [compose_eq_root _ _ hch]
    simp only [root, outCell, List.getLast?_map, getD_map]
    rfl

/-! ## The node key and the program's cells in a trace -/

/-- The kind of a node's children (`ChildKind`). -/
inductive Kind where
  | app
  | node

/-- **The pinned node key's shape**: `build_agg`'s build-time facts. -/
structure NodeKey where
  k : Nat
  two_le : 2 ≤ k
  nCtx : Nat
  nState : Nat
  kind : Kind

/-- **The node program's cells in a trace** (the decode's fixed coordinate projection): per child,
the statement cells, the child proof and its public values from `build_verifier`, and the digest
cells of its `hash_range` job; plus the digest cells of `out`. -/
structure NodeRead (K : NodeKey) (Dg Proof : Type) where
  ctx : Fin K.k → Fin K.nCtx → Fp
  a : Fin K.k → Fp
  e : Fin K.k → Fp
  sa : Fin K.k → Fin K.nState → Fp
  se : Fin K.k → Fin K.nState → Fp
  proof : Fin K.k → Proof
  pv : Fin K.k → List Fp
  kidDig : Fin K.k → Dg
  outDig : Dg

variable {K : NodeKey} {α Dg Proof : Type}

def NodeRead.cell (R : NodeRead K Dg Proof) (i : Fin K.k) : SCell :=
  ⟨List.ofFn (R.ctx i), R.a i, R.e i, List.ofFn (R.sa i), List.ofFn (R.se i)⟩

def NodeRead.cells (R : NodeRead K Dg Proof) : List SCell := List.ofFn R.cell

/-- The children the node's decode hands to the native node program: the denoted statement and
the proof, in order. -/
def NodeRead.kids (enc : List Fp → α) (R : NodeRead K Dg Proof) : List (Stmt α × Proof) :=
  List.ofFn fun i => ((R.cell i).stmt enc, R.proof i)

theorem NodeRead.shape (R : NodeRead K Dg Proof) : ∀ c ∈ R.cells, Shape K.nCtx K.nState c := by
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc
  simp [NodeRead.cell, Shape]

theorem NodeRead.cells_ne (R : NodeRead K Dg Proof) : R.cells ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [NodeRead.cells] at this
  have := K.two_le
  omega

theorem NodeRead.kids_map (enc : List Fp → α) (R : NodeRead K Dg Proof) :
    (R.kids enc).map Prod.fst = R.cells.map (SCell.stmt enc) := by
  simp [NodeRead.kids, NodeRead.cells, List.map_ofFn, Function.comp_def]

/-! ## The four per-trace components of the node program -/

section Node

variable (enc : List Fp → α) (rdigest : Stmt α → Dg) (InnerAcc : Proof → List Fp → Prop)
  (pvDig : List Fp → Dg) (segStmt : List Fp → Stmt α)

/-- **(1) SHA.** Each `hash_range` job's digest cells are the native tag-9 digest of the statement
its message cells denote: the children's preimages (node children) and `out`. -/
def NodeSha (R : NodeRead K Dg Proof) : Prop :=
  (K.kind = .node → ∀ i, R.kidDig i = rdigest ((R.cell i).stmt enc)) ∧
    R.outDig = rdigest ((outCell R.cells).stmt enc)

/-- **(2 + 4, recursive) The in-circuit verifier.** Each `build_verifier` gadget means that the
native verifier of the child's key accepts the child proof with those public values. This
includes program binding of node children. -/
def NodeInner (R : NodeRead K Dg Proof) : Prop :=
  ∀ i, InnerAcc (R.proof i) (R.pv i)

/-- **(3) The tape.** The public digest the decode reads is the `pv_digest` cells. -/
def NodeTape (pubDig : List Fp → Dg) (R : NodeRead K Dg Proof) (pub : List Fp) : Prop :=
  pubDig pub = R.outDig

/-- **(4) The asserts.** The statement link per child kind (app: the cells are `of_segment` of
the child's public values; node: the preimage digest equals the child's exposed digest) and the
continuity loop. -/
def NodeAsserts (R : NodeRead K Dg Proof) : Prop :=
  (match K.kind with
    | .app => ∀ i, (R.cell i).stmt enc = segStmt (R.pv i)
    | .node => ∀ i, R.kidDig i = pvDig (R.pv i)) ∧
  ContAsserts R.cells

/-- The native acceptance of a child, as the node's children are checked (`check_range_statement`
for node children, `of_segment` for app children): what `Acc` must contain. -/
def AccNative (Acc : Stmt α → Proof → Prop) : Prop :=
  (∀ π pv, InnerAcc π pv → Acc (segStmt pv) π) ∧
    (∀ π pv st, InnerAcc π pv → pvDig pv = rdigest st → Acc st π)

/-- The node's decode: public digest from the public values, the children from the read. -/
def nodeDecode {Params : Type} (R : Trace Fp → NodeRead K Dg Proof) (pubDig : List Fp → Dg)
    (par : Trace Fp → Params) : NvDecode Dg (List (Stmt α × Proof)) Params where
  stmt := pubDig
  proof tr := (R tr).kids enc
  params := par

variable [DecidableEq α]

/-- **Sub-obligation 6 for the node: the composition.** A read satisfying the four components
is accepted by the native node program on the decoded statement and children. -/
theorem node_composition {Params : Type} (Acc : Stmt α → Proof → Prop)
    (hAcc : AccNative rdigest InnerAcc pvDig segStmt Acc) (pubDig : List Fp → Dg)
    (R : NodeRead K Dg Proof) (pub : List Fp) (q : Params)
    (hS : NodeSha enc rdigest R) (hI : NodeInner InnerAcc R) (hT : NodeTape pubDig R pub)
    (hA : NodeAsserts enc pvDig segStmt R) :
    (aggNodeV (Params := Params) Acc rdigest).accepts (pubDig pub) (R.kids enc) q PUnit.unit := by
  refine ⟨?_, ?_, (outCell R.cells).stmt enc, ?_, ?_⟩
  · simp [NodeRead.kids, K.two_le]
  · intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc
    obtain ⟨hlink, -⟩ := hA
    cases hk : K.kind with
    | app =>
      rw [hk] at hlink
      have := hAcc.1 _ _ (hI i)
      rw [← hlink i] at this
      exact this
    | node =>
      rw [hk] at hlink
      exact hAcc.2 _ _ _ (hI i) ((hlink i).symm.trans (hS.1 hk i))
  · rw [NodeRead.kids_map]
    exact compose_of_asserts enc K.nCtx K.nState _ R.cells_ne R.shape hA.2
  · rw [hT, hS.2]

/-- **What remains for the node: the AIR executes the program.** On every trace satisfying the
pinned NvAir with the LogUp balance, the program's cells satisfy the four components. This is
generic NV faithfulness (sub-obligations 1–4) at this program, and it is open: there is no Lean
model of NvAir. -/
def NodeExec (Pin : NvPinned) (R : Trace Fp → NodeRead K Dg Proof) (pubDig : List Fp → Dg) :
    Prop :=
  ∀ tr pub, HoldsLogUp Pin.air pub tr →
    NodeSha enc rdigest (R tr) ∧ NodeInner InnerAcc (R tr) ∧ NodeTape pubDig (R tr) pub ∧
      NodeAsserts enc pvDig segStmt (R tr)

/-- **`NvFaithful` for the pinned node program from `NodeExec`.** -/
theorem nvFaithful_node {Params : Type} (Pin : NvPinned) (Acc : Stmt α → Proof → Prop)
    (hAcc : AccNative rdigest InnerAcc pvDig segStmt Acc) (R : Trace Fp → NodeRead K Dg Proof)
    (pubDig : List Fp → Dg) (par : Trace Fp → Params)
    (hX : NodeExec enc rdigest InnerAcc pvDig segStmt Pin R pubDig) :
    NvFaithful Pin (nodeDecode enc R pubDig par) (aggNodeV Acc rdigest) := by
  intro tr pub h
  obtain ⟨hS, hI, hT, hA⟩ := hX tr pub h
  exact ⟨PUnit.unit, node_composition enc rdigest InnerAcc pvDig segStmt Acc hAcc pubDig (R tr)
    pub (par tr) hS hI hT hA⟩

/-- **The node's composition in the generic form** (`NvCompositionAt` of `NvFaithful.lean`, with
its `HoldsLogUp` premise). The node's components fill the generic slots:
* SHA (1) fills `limbsOK` with the tag-9 jobs;
* the tape (3) fills `tapeOf`/`stmtVec` with the digest cells under an injective cell encoding
  `encD`;
* the asserts and the inner verifiers (4) fill `arithOK`.

The transcript slot (2) and the program slot are not used at this level: the children's T*
transcripts and program binding are inside `NodeInner`. -/
theorem nvComposition_node {Params : Type} (Pin : NvPinned) (Acc : Stmt α → Proof → Prop)
    (hAcc : AccNative rdigest InnerAcc pvDig segStmt Acc) (R : Trace Fp → NodeRead K Dg Proof)
    (pubDig : List Fp → Dg) (par : Trace Fp → Params) (encD : Dg → List Fp)
    (hEnc : ∀ x y, encD x = encD y → x = y)
    (sha : ShaSpec) (digestOf : Trace Fp → List Nat → List Nat)
    (circuitSample : Trace Fp → Nat → List Fp) (nativeSample : List Fp → Nat → List Fp)
    (tInit : List Fp) (programOf : Trace Fp → List Nat) (pinnedProgram : List Nat) :
    NvComposition Pin (nodeDecode enc R pubDig par) (aggNodeV Acc rdigest) sha digestOf
      (fun tr => NodeSha enc rdigest (R tr)) circuitSample nativeSample tInit programOf
      pinnedProgram (fun tr => encD (R tr).outDig) encD
      (fun tr _ _ _ => NodeAsserts enc pvDig segStmt (R tr) ∧ NodeInner InnerAcc (R tr)) := by
  intro tr pub h hSha _ hProg hAr _
  have hT : NodeTape pubDig (R tr) pub := (hEnc _ _ (hProg h).2).symm
  exact node_composition enc rdigest InnerAcc pvDig segStmt Acc hAcc pubDig (R tr) pub (par tr)
    (hSha h).1 (hAr h).2 hT (hAr h).1

end Node

/-! ## The wrap program

Plan §3.4: the wrap verifies the root proof, and checks the root statement against the public
statement (`ctx`, `B_0 = Init`, `B_N` final). The wrap is not built yet, so this is the plan's
program at the level of `aggWrapV`. The root's statement is loaded as cells, and its tag-9 job
must equal the root's exposed digest, exactly as for a node child. -/

section Wrap

variable (enc : List Fp → α) (rdigest : Stmt α → Dg) (InnerAcc : Proof → List Fp → Prop)
  (pvDig : List Fp → Dg) (segStmt : List Fp → Stmt α)

/-- The wrap program's cells in a trace: the root statement cells, the root proof and public
values, and the digest of the root statement's `hash_range` job. -/
structure WrapRead (nCtx nState : Nat) (Dg Proof : Type) where
  ctx : Fin nCtx → Fp
  a : Fp
  e : Fp
  sa : Fin nState → Fp
  se : Fin nState → Fp
  proof : Proof
  pv : List Fp
  rootDig : Dg

def WrapRead.cell {nCtx nState : Nat} (R : WrapRead nCtx nState Dg Proof) : SCell :=
  ⟨List.ofFn R.ctx, R.a, R.e, List.ofFn R.sa, List.ofFn R.se⟩

/-- The wrap's decode: the public statement from the public values; the root statement and
proof from the read. -/
def wrapDecode {nCtx nState : Nat} {ParamsW : Type} (R : Trace Fp → WrapRead nCtx nState Dg Proof)
    (pubS : List Fp → PublicStmt) (par : Trace Fp → ParamsW) :
    NvDecode PublicStmt (Stmt α × Proof) ParamsW where
  stmt := pubS
  proof tr := ((R tr).cell.stmt enc, (R tr).proof)
  params := par

/-- The wrap's four components on a read, at public statement `s`:
* SHA (1): the root's `hash_range` job is the native digest;
* the inner verifier (2 + 4);
* the asserts (4): the root digest link and the three statement checks.

The tape (3) is the decode's `pubS`. -/
def WrapComp {nCtx nState : Nat} (ctxOf : PublicStmt → α) (InitOK FinalOK : PublicStmt → α → Prop)
    (R : WrapRead nCtx nState Dg Proof) (s : PublicStmt) : Prop :=
  R.rootDig = rdigest (R.cell.stmt enc) ∧ InnerAcc R.proof R.pv ∧
    R.rootDig = pvDig R.pv ∧ (R.cell.stmt enc).ctx = ctxOf s ∧
      InitOK s (R.cell.stmt enc).sa ∧ FinalOK s (R.cell.stmt enc).se

/-- **Sub-obligation 6 for the wrap: the composition.** -/
theorem wrap_composition {nCtx nState : Nat} {ParamsW : Type} (Acc : Stmt α → Proof → Prop)
    (hAcc : AccNative rdigest InnerAcc pvDig segStmt Acc) (ctxOf : PublicStmt → α)
    (InitOK FinalOK : PublicStmt → α → Prop) (R : WrapRead nCtx nState Dg Proof) (s : PublicStmt)
    (q : ParamsW) (h : WrapComp enc rdigest InnerAcc pvDig ctxOf InitOK FinalOK R s) :
    (aggWrapV (Params := ParamsW) Acc ctxOf InitOK FinalOK).accepts s (R.cell.stmt enc, R.proof) q
      PUnit.unit := by
  obtain ⟨hS, hI, hL, hc, hi, hf⟩ := h
  exact ⟨hAcc.2 _ _ _ hI (hL.symm.trans hS), hc, hi, hf⟩

/-- **What remains for the wrap**: the AIR executes the wrap program (open, as `NodeExec`). -/
def WrapExec {nCtx nState : Nat} (PinW : NvPinned) (ctxOf : PublicStmt → α)
    (InitOK FinalOK : PublicStmt → α → Prop) (R : Trace Fp → WrapRead nCtx nState Dg Proof)
    (pubS : List Fp → PublicStmt) : Prop :=
  ∀ tr pub, HoldsLogUp PinW.air pub tr →
    WrapComp enc rdigest InnerAcc pvDig ctxOf InitOK FinalOK (R tr) (pubS pub)

/-- **`NvFaithful` for the wrap program from `WrapExec`.** -/
theorem nvFaithful_wrap {nCtx nState : Nat} {ParamsW : Type} (PinW : NvPinned)
    (Acc : Stmt α → Proof → Prop) (hAcc : AccNative rdigest InnerAcc pvDig segStmt Acc)
    (ctxOf : PublicStmt → α) (InitOK FinalOK : PublicStmt → α → Prop)
    (R : Trace Fp → WrapRead nCtx nState Dg Proof) (pubS : List Fp → PublicStmt)
    (par : Trace Fp → ParamsW)
    (hX : WrapExec enc rdigest InnerAcc pvDig PinW ctxOf InitOK FinalOK R pubS) :
    NvFaithful PinW (wrapDecode enc R pubS par) (aggWrapV Acc ctxOf InitOK FinalOK) :=
  fun tr pub h => ⟨PUnit.unit, wrap_composition enc rdigest InnerAcc pvDig segStmt Acc hAcc ctxOf
    InitOK FinalOK (R tr) (pubS pub) (par tr) (hX tr pub h)⟩

end Wrap

/-! ## `LeafHolds`: discharged by the circuit's segment system -/

/-- **The circuit's segment system.** Templates, boundaries and abstraction come from `S0`. A
segment instance is a template trace that satisfies the template's AIR (`Holds`, the natural
balance the segment lanes prove against), at public values whose statement has the instance's
boundaries. -/
def circSeg (S0 : SegSystem) (segAir : S0.Template → Air) (segStmt : List Fp → Stmt S0.Bnd) :
    SegSystem where
  Template := S0.Template
  Bnd := S0.Bnd
  Trace := List Fp × Trace Fp
  abs := S0.abs
  Holds k b b' t := ZkFormal.Air.Holds (segAir k) t.1 t.2 ∧ (segStmt t.1).sa = b ∧
    (segStmt t.1).se = b'

/-- **`LeafHolds` is a theorem** for every aggregation interface over the circuit's segment
system whose leaf templates and statement decode are the system's. -/
theorem leafHolds_circ (S0 : SegSystem) (segAir : S0.Template → Air)
    (segStmt : List Fp → Stmt S0.Bnd) (A : AggNode (circSeg S0 segAir segStmt))
    (h1 : ∀ k, A.segAir k = segAir k) (h2 : ∀ p, A.segStmt p = segStmt p) : LeafHolds A := by
  intro k pubv tr hl
  refine ⟨(pubv, tr), ?_⟩
  show ZkFormal.Air.Holds (segAir k) pubv tr ∧ (segStmt pubv).sa = (A.segStmt pubv).sa ∧
    (segStmt pubv).se = (A.segStmt pubv).se
  rw [h2, ← h1]
  exact ⟨holds_of_holdsLogUp hl, rfl, rfl⟩

/-! ## `RangeBinding`: reduced to collision resistance -/

/-- **The pinned range message** (`range_values`): `[n_ctx, n_state, ctx.., a, e, s_a.., s_e..]`,
with the boundary vectors encoded by `encB`. -/
def rmsg (encB : α → List Nat) (st : Stmt α) : List Nat :=
  [(encB st.ctx).length, (encB st.sa).length] ++ encB st.ctx ++ [st.a, st.e] ++ encB st.sa ++
    encB st.se

/-- **The range message is injective** for any injective boundary encoding. The two length
prefixes make it self-delimiting; `s_e` is whatever remains. -/
theorem rmsg_inj (encB : α → List Nat) (hinj : ∀ x y, encB x = encB y → x = y) :
    ∀ s t : Stmt α, rmsg encB s = rmsg encB t → s = t := by
  rintro ⟨c, a, e, sa, se⟩ ⟨c', a', e', sa', se'⟩ h
  simp only [rmsg, List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨hl1, hl2, h⟩ := h
  obtain ⟨hc, h⟩ := List.append_inj h hl1
  simp only [List.cons.injEq] at h
  obtain ⟨ha, he, h⟩ := h
  obtain ⟨hsa, hse⟩ := List.append_inj h hl2
  rw [hinj _ _ hc, hinj _ _ hsa, hinj _ _ hse, ha, he]

/-- A collision of a function. -/
def HColl {β γ : Type} (H : β → γ) : Prop := ∃ m m', m ≠ m' ∧ H m = H m'

/-- **`RangeBinding` from collision resistance.** If the range digest is `H` of the pinned
message, and an `H` collision is the bad event `rangeColl`, then the digest is binding. -/
theorem rangeBinding_of {S : SegSystem} (A : AggNode S) (BE : BadEvents) (H : List Nat → A.Dg)
    (encB : S.Bnd → List Nat) (hinj : ∀ x y, encB x = encB y → x = y)
    (hR : ∀ st, A.rdigest st = H (rmsg encB st)) (hBE : HColl H → BE.rangeColl) :
    RangeBinding A BE := by
  classical
  intro a b h
  by_cases hab : a = b
  · exact .inl hab
  · exact .inr (hBE ⟨rmsg encB a, rmsg encB b, fun e => hab (rmsg_inj encB hinj a b e),
      by rw [← hR, ← hR, h]⟩)

/-- **An `H` collision is a 42-B SHA-384 collision** when `H` is `bdigest` (SHA-384 truncated to
42 bytes, `Boundary.lean`) after an injective serialisation, e.g. tag 9 and the field bytes. -/
theorem hColl_bdigest (ser : List Nat → ArenaCore.Bytes) (hser : ∀ x y, ser x = ser y → x = y) :
    HColl (fun m => NearSpecV3.E2E.Bnd.bdigest (ser m)) → HColl NearSpecV3.E2E.Bnd.bdigest := by
  rintro ⟨m, m', hne, h⟩
  exact ⟨ser m, ser m', fun e => hne (hser _ _ e), h⟩

/-! ## The E2E statement with the node, wrap and leaf obligations reduced -/

/-- **`e2e_sound` from the AIR-execution obligations.** `NvFaithful` of the node and of the wrap
come from `NodeExec`/`WrapExec`, which state that the AIR executes the program. `LeafHolds` is
proved over the circuit's segment system, and `RangeBinding` comes from collision resistance of the
range hash. What remains: `NodeExec`, `WrapExec`, `ExtractWG`/`ExtractW` (QROM), the definitional
facts `AccNative` and the decodes, obligation 1b, 2 and 4. -/
theorem e2e_sound_of_exec {S0 : SegSystem} [DecidableEq S0.Bnd] (segAir : S0.Template → Air)
    (segStmt : List Fp → Stmt S0.Bnd) (A : AggNode (circSeg S0 segAir segStmt))
    (hsegAir : ∀ k, A.segAir k = segAir k) (hsegStmt : ∀ p, A.segStmt p = segStmt p)
    (Wr : AggWrap A) (W : WrapCheck (circSeg S0 segAir segStmt)) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (BE : BadEvents)
    -- the node program
    {K : NodeKey} (enc : List Fp → S0.Bnd) (InnerAcc : A.Proof → List Fp → Prop)
    (pvDig : List Fp → A.Dg) (hAcc : AccNative A.rdigest InnerAcc pvDig segStmt A.Acc)
    (R : Trace Fp → NodeRead K A.Dg A.Proof) (pubDig : List Fp → A.Dg)
    (par : Trace Fp → A.Params) (hD : A.D = nodeDecode enc R pubDig par)
    (hX : NodeExec enc A.rdigest InnerAcc pvDig segStmt A.Pin R pubDig)
    -- the wrap program
    {nCtx nState : Nat} (RW : Trace Fp → WrapRead nCtx nState A.Dg A.Proof)
    (pubS : List Fp → PublicStmt) (parW : Trace Fp → Wr.ParamsW)
    (hDW : Wr.DW = wrapDecode enc RW pubS parW)
    (hXW : WrapExec enc A.rdigest InnerAcc pvDig Wr.PinW Wr.ctxOf W.InitOK W.FinalOK RW pubS)
    -- the range digest
    (H : List Nat → A.Dg) (encB : S0.Bnd → List Nat) (hinj : ∀ x y, encB x = encB y → x = y)
    (hR : ∀ st, A.rdigest st = H (rmsg encB st)) (hBE : HColl H → BE.rangeColl)
    -- extraction and the remaining obligations
    (hEx : ExtractWG A BE) (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (hExW : ExtractW Wr extW pubW FinalVerify BE)
    (ob1b : WrapFinalFaithful (circSeg S0 segAir segStmt) W)
    (ob2 : SegSound (circSeg S0 segAir segStmt) BE.Any)
    (ob4 : WitnessExtraction (circSeg S0 segAir segStmt) W BE.Any)
    (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) : E2EStmt s ∨ BE.Any := by
  letI : DecidableEq (circSeg S0 segAir segStmt).Bnd := ‹DecidableEq S0.Bnd›
  have hNv : NvFaithful A.Pin A.D (aggNodeV (Params := A.Params) A.Acc A.rdigest) := by
    rw [hD]
    exact nvFaithful_node enc A.rdigest InnerAcc pvDig segStmt A.Pin A.Acc hAcc R pubDig par hX
  have hNvW : NvFaithful Wr.PinW Wr.DW
      (aggWrapV (Params := Wr.ParamsW) A.Acc Wr.ctxOf W.InitOK W.FinalOK) := by
    rw [hDW]
    exact nvFaithful_wrap enc A.rdigest InnerAcc pvDig segStmt Wr.PinW A.Acc hAcc Wr.ctxOf
      W.InitOK W.FinalOK RW pubS parW hXW
  exact e2e_sound_of_agg A Wr W FinalVerify BE hNv hNvW hEx extW pubW hExW
    (leafHolds_circ S0 segAir segStmt A hsegAir hsegStmt)
    (rangeBinding_of A BE H encB hinj hR hBE) ob1b ob2 ob4 s π hv

/-! ## Non-vacuity

A two-child app node over `Fin`-indexed cells (`n_ctx = 1`, `n_state = 1`, boundaries `0 → 1 → 2`)
satisfies the continuity asserts. With the children swapped it does not: the boundary continuity
assert `zip(s_a_1, s_e_0)` fails. -/

def exCells : List SCell := [⟨[7], 0, 1, [0], [1]⟩, ⟨[7], 1, 2, [1], [2]⟩]

example : ContAsserts exCells := by
  intro i h
  have : i = 0 := by simp [exCells] at h; omega
  subst this
  refine ⟨?_, rfl, ?_⟩ <;> intro p hp <;> simp [exCells] at hp <;> subst hp <;> rfl

example : ¬ ContAsserts exCells.reverse := by
  intro h
  have := (h 0 (by simp [exCells])).2.2 (0, 2) (by simp [exCells])
  exact absurd this (by decide)

example : compose (exCells.map (SCell.stmt id)) = some ((outCell exCells).stmt id) := by
  refine compose_of_asserts id 1 1 exCells (by simp [exCells]) ?_ ?_
  · intro c hc; simp [exCells] at hc; rcases hc with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  · intro i h
    have : i = 0 := by simp [exCells] at h; omega
    subst this
    refine ⟨?_, rfl, ?_⟩ <;> intro p hp <;> simp [exCells] at hp <;> subst hp <;> rfl

#print axioms zipEq_eq
#print axioms compose_of_asserts
#print axioms node_composition
#print axioms nvFaithful_node
#print axioms nvComposition_node
#print axioms wrap_composition
#print axioms nvFaithful_wrap
#print axioms leafHolds_circ
#print axioms rmsg_inj
#print axioms rangeBinding_of
#print axioms hColl_bdigest
#print axioms e2e_sound_of_exec

end ZkFormal.PQ.E2ENode
