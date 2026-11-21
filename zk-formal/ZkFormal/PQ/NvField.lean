import ZkFormal.PQ.NvTape
import ZkFormal.PQ.NvCircuitExport
import ZkFormal.PQ.E2EHold

/-!
# ZkFormal.PQ.NvField — the NV circuit's own trace predicate (field-count interactions)

Lane E (E2E M11g, item 1), 2026-11-04.

M11f found that NvAir's interactions carry **field-valued counts merged across roles** (the
mem slot 0 count is `−ka·mult + kb`), so `HoldsLogUp` over a `ZkFormal.Air` transcription
(natural multiplicities with a send flag) is not the circuit's predicate. This file states the
backend's semantics for the **whole pinned circuit** and restates `NodeExec` over it.

## The semantics (`FTable`, `FHolds`)

* A table is a list of constraint expressions and a list of interactions `(bus, count, message)`
  whose count is an arbitrary expression evaluated in `Fp` (the backend's `count`, signed:
  `send`/`lookup_key` `+enabled`, `receive`/`add_key_with_lookups` `−count`).
* `FHolds A pub tr`: every constraint of table `t` vanishes on every row of table `t`, and for
  **every bus `b` and message `m`**, the field sum of the counts of all entries of all tables on
  bus `b` with message `m` is `0` (LogUp-GKR's balance as the extractor gives it, modulo
  `gkrBad`). Public values: table 0 (NvAir) reads `pub`, the others none.
* `nvCircuit`: the four pinned tables, **all exported** (`NvAirExport.lean`: NvAir;
  `NvCircuitExport.lean`: Sha512Air4, TableAir4, ByteAir, from `nv_export_all`), each expression
  the exported DAG node.
* `NvHold pub tr := FHolds nvCircuit pub tr ∧ tr.log 0 ≤ 24 ∧ ∀ t < 4, tr.log t ≤ 27` (NvAir's
  height is at most `2^ADDR_BITS`, pinned in the vk; every height within the two-adicity).

## Proved

* `nvConstr_of`, `memBalance_of`: `NvHold` gives `NvTape`'s `NvConstr` and `MemBalance` (the mem
  bus has no entries outside NvAir: `mem_only_nv`, from the exported interaction lists).
* `busUsers_exported`: the bus listing `NvTape.busUsers` (and hence the vacuity guard
  `nv_closure`) is the exported one, computed from the four exported interaction lists.
* `nodeTape_of_hold`: `NodeTape` from `NvHold` and the program's two `PvD` rows (`TapeAt`).
* `NodeExecV` (`= E2EHold.NodeExecH NvHold`), `nodeExecV_of`: the node's execution obligation over
  the circuit's predicate, with the tape component discharged; `nvFaithfulV_node`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace ZkFormal.PQ.NvField

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.NvAirExport ZkFormal.PQ.NvCircuitExport
open ZkFormal.PQ.NvTape ZkFormal.PQ.E2ENode ZkFormal.PQ.E2EHold ZkFormal.PQ.Nv ZkFormal.PQ.E2EAgg
open ZkFormal.PQ.Aggregation.Stmt

set_option maxRecDepth 100000

/-! ## Field-count tables -/

/-- An interaction with a field-valued count expression. -/
structure FInt where
  bus : Nat
  count : Expr
  msg : List Expr

/-- A table: constraints and field-count interactions. -/
structure FTable where
  cons : List Expr
  ints : List FInt

/-- Node `i` of a DAG node list as an expression (children have smaller indices). -/
def toExprOf (nodes : List DagNode) : Nat → Nat → Expr
  | 0, _ => .const 0
  | f + 1, i =>
    match nodes.getD i (.k 0) with
    | .v c nx => .col c nx
    | .p j => .pub j
    | .k n => .const n
    | .add a b => .add (toExprOf nodes f a) (toExprOf nodes f b)
    | .sub a b => .add (toExprOf nodes f a) (.neg (toExprOf nodes f b))
    | .mul a b => .mul (toExprOf nodes f a) (toExprOf nodes f b)
    | .neg a => .neg (toExprOf nodes f a)
    | .first => .isFirst
    | .last => .isLast
    | .trans => .isTransition

/-- The exported node `i` of a DAG. -/
def dagOf (nodes : List DagNode) (i : Nat) : Expr := toExprOf nodes (i + 1) i

theorem toExpr_eq : ∀ f i, NvTape.toExpr f i = toExprOf nvNodes f i
  | 0, _ => rfl
  | f + 1, i => by
    simp only [NvTape.toExpr, toExprOf, NvTape.node]
    cases nvNodes.getD i (DagNode.k 0) <;> simp only [toExpr_eq f]

/-- NvAir's nodes are `NvTape.dag`. -/
theorem dagOf_nv : dagOf nvNodes = dag := funext fun i => (toExpr_eq (i + 1) i).symm

/-- A table from an exported DAG. -/
def tableOf (nodes : List DagNode) (cons : List Nat) (ints : List (Nat × Nat × List Nat)) :
    FTable :=
  ⟨cons.map (dagOf nodes), ints.map fun x => ⟨x.1, dagOf nodes x.2.1, x.2.2.map (dagOf nodes)⟩⟩

/-- **The pinned NV circuit**: NvAir, Sha512Air4, TableAir4, ByteAir (keygen order). -/
def nvCircuit : List FTable :=
  [tableOf nvNodes nvConstraintIdx nvInteractionIdx,
   tableOf shaNodes shaConstraintIdx shaInteractionIdx,
   tableOf tabNodes tabConstraintIdx tabInteractionIdx,
   tableOf byteNodes byteConstraintIdx byteInteractionIdx]

/-- Public values of table `t`: NvAir's, none for the others. -/
def pubOf (pub : List Fp) (t : Nat) : List Fp := if t = 0 then pub else []

/-- The entries `(count, message)` of table `T` (index `t`) on bus `b`, every row. -/
def tEntries (T : FTable) (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat) :
    List (Fp × List Fp) :=
  (List.range (tr.height t)).flatMap fun r =>
    (T.ints.filter fun i => i.bus == b).map fun i =>
      (i.count.eval tr t r pub, i.msg.map fun e => e.eval tr t r pub)

/-- All entries on bus `b`. -/
def busEntries (A : List FTable) (tr : Trace Fp) (pub : List Fp) (b : Nat) : List (Fp × List Fp) :=
  (List.range A.length).flatMap fun t => tEntries (A.getD t ⟨[], []⟩) tr t (pubOf pub t) b

/-- **The backend's trace predicate**: constraints on every row, the field LogUp balance on every
bus. -/
structure FHolds (A : List FTable) (pub : List Fp) (tr : Trace Fp) : Prop where
  constr : ∀ t, t < A.length → ∀ r, r < tr.height t → ∀ e ∈ (A.getD t ⟨[], []⟩).cons,
    e.eval tr t r (pubOf pub t) = 0
  bal : ∀ b m, fsumAt m (busEntries A tr pub b) = 0

/-- **The NV circuit's trace predicate**: `FHolds` for the pinned four tables; NvAir's height at
most `2^24` (`ADDR_BITS`; the vk pins the heights) and every height within BabyBear's two-adicity
`2^27` (the PCS domain). -/
def NvHold (pub : List Fp) (tr : Trace Fp) : Prop :=
  FHolds nvCircuit pub tr ∧ tr.log 0 ≤ 24 ∧ ∀ t, t < 4 → tr.log t ≤ 27

/-! ## From `NvHold` to `NvTape`'s predicates -/

theorem nvConstr_of {pub : List Fp} {tr : Trace Fp} (h : NvHold pub tr) : NvConstr tr 0 pub := by
  intro r hr j hj
  have := h.1.constr 0 (by decide) r hr (dag j) (List.mem_map.2 ⟨j, hj, by rw [dagOf_nv]⟩)
  exact this

theorem height_le {tr : Trace Fp} (h : tr.log 0 ≤ 24) : tr.height 0 ≤ 2 ^ 24 :=
  Nat.pow_le_pow_right (by decide) h

/-- No table but NvAir has a mem-bus (bus 3) interaction (exported lists). -/
theorem mem_only_nv : (shaInteractionIdx.filter fun x => x.1 == 3) = [] ∧
    (tabInteractionIdx.filter fun x => x.1 == 3) = [] ∧
    (byteInteractionIdx.filter fun x => x.1 == 3) = [] := by decide

theorem nv_mem_filter : (nvInteractionIdx.filter fun x => x.1 == 3) =
    [(3, 4171, [4144, 4146, 4148, 4150, 4152, 4154, 4156, 4158, 4160, 4162, 4164, 4166, 4168]),
     (3, 4229, [4174, 4177, 4180, 4183, 4186, 4189, 4192, 4195, 4198, 4201, 4204, 4207, 4210]),
     (3, 4281, [4233, 4236, 4239, 4242, 4245, 4248, 4251, 4254, 4257, 4260, 4263, 4266, 4269])] := by
  decide

theorem tableOf_filter (nodes : List DagNode) (cons : List Nat) (ints : List (Nat × Nat × List Nat))
    (b : Nat) : ((tableOf nodes cons ints).ints.filter fun i => i.bus == b) =
      (ints.filter fun x => x.1 == b).map
        fun x => ⟨x.1, dagOf nodes x.2.1, x.2.2.map (dagOf nodes)⟩ := by
  simp only [tableOf, List.filter_map]
  rfl

theorem tEntries_nil (T : FTable) (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat)
    (h : (T.ints.filter fun i => i.bus == b) = []) : tEntries T tr t pub b = [] := by
  simp [tEntries, h]

/-- **The mem bus of `nvCircuit` is NvAir's `memEntries`.** -/
theorem busEntries_mem (tr : Trace Fp) (pub : List Fp) :
    busEntries nvCircuit tr pub 3 = memEntries tr 0 pub := by
  have e1 : tEntries (nvCircuit.getD 1 ⟨[], []⟩) tr 1 (pubOf pub 1) 3 = [] :=
    tEntries_nil _ _ _ _ _ (by
      show ((tableOf shaNodes shaConstraintIdx shaInteractionIdx).ints.filter _) = []
      rw [tableOf_filter, mem_only_nv.1]; rfl)
  have e2 : tEntries (nvCircuit.getD 2 ⟨[], []⟩) tr 2 (pubOf pub 2) 3 = [] :=
    tEntries_nil _ _ _ _ _ (by
      show ((tableOf tabNodes tabConstraintIdx tabInteractionIdx).ints.filter _) = []
      rw [tableOf_filter, mem_only_nv.2.1]; rfl)
  have e3 : tEntries (nvCircuit.getD 3 ⟨[], []⟩) tr 3 (pubOf pub 3) 3 = [] :=
    tEntries_nil _ _ _ _ _ (by
      show ((tableOf byteNodes byteConstraintIdx byteInteractionIdx).ints.filter _) = []
      rw [tableOf_filter, mem_only_nv.2.2]; rfl)
  have e0 : tEntries (nvCircuit.getD 0 ⟨[], []⟩) tr 0 (pubOf pub 0) 3 = memEntries tr 0 pub := by
    show tEntries (tableOf nvNodes nvConstraintIdx nvInteractionIdx) tr 0 pub 3 = _
    unfold tEntries memEntries
    rw [tableOf_filter, nv_mem_filter, memIdx_eq, dagOf_nv]
    simp only [List.map_cons, List.map_nil]
  have hr : List.range nvCircuit.length = [0, 1, 2, 3] := rfl
  unfold busEntries
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, e0, e1, e2, e3, List.append_nil]

theorem memBalance_of {pub : List Fp} {tr : Trace Fp} (h : NvHold pub tr) :
    MemBalance tr 0 pub := by
  intro m
  have := h.1.bal 3 m
  rwa [busEntries_mem] at this

/-! ## The bus listing (vacuity guard) is the exported one -/

/-- **`NvTape.busUsers` is computed from the four exported interaction lists**, so `nv_closure`
(the tables that balance NvAir's buses are exactly the four of `nvCircuit`) is about the export. -/
def busesOf (l : List (Nat × Nat × List Nat)) (b : Nat) : Bool := l.any (·.1 == b)

theorem busUsers_exported : busUsers.map (·.1) = ["NvAir", "Sha512Air4", "TableAir4", "ByteAir"] ∧
    (∀ b, b < 16 → busUsers.map (fun p => p.2.contains b) =
      [busesOf nvInteractionIdx b, busesOf shaInteractionIdx b, busesOf tabInteractionIdx b,
        busesOf byteInteractionIdx b]) ∧
    (nvInteractionIdx ++ shaInteractionIdx ++ tabInteractionIdx ++ byteInteractionIdx).all
      (·.1 < 16) = true := by decide

/-! ## The tape component over `NvHold` -/

/-- **The program's two `PvD` rows** (the tape layout of a decode `dec`): rows `dlo`, `dhi` are
`PvD` rows reading addresses `alo`, `ahi` (halves 0 / 1), and the decode's `outDig` is `dec` of
the cells at those addresses. -/
def TapeAt {K : NodeKey} {Dg Proof : Type} (dec : List Fp → Dg) (tr : Trace Fp)
    (R : NodeRead K Dg Proof) : Prop :=
  ∃ dlo dhi alo ahi, PvdAt tr 0 dlo alo 0 ∧ PvdAt tr 0 dhi ahi 1 ∧ alo < 2 ^ 24 ∧ ahi < 2 ^ 24 ∧
    R.outDig = dec (digCells tr 0 alo ahi)

/-- **`NodeTape` from the circuit's predicate.** -/
theorem nodeTape_of_hold {K : NodeKey} {Dg Proof : Type} (dec : List Fp → Dg) {tr : Trace Fp}
    {pub : List Fp} (R : NodeRead K Dg Proof) (h : NvHold pub tr) (hT : TapeAt dec tr R) :
    NodeTape (fun p => dec (pvDigest p)) R pub := by
  obtain ⟨dlo, dhi, alo, ahi, hlo, hhi, halo, hahi, hR⟩ := hT
  exact nodeTape_of_pvd dec R (nvConstr_of h) (memBalance_of h) (height_le h.2.1) hlo hhi halo hahi hR

/-! ## `NodeExec` over the circuit's predicate -/

section Node

variable {K : NodeKey} {α Dg Proof : Type} (enc : List Fp → α) (rdigest : Stmt α → Dg)
  (InnerAcc : Proof → List Fp → Prop) (pvDig : List Fp → Dg) (segStmt : List Fp → Stmt α)

/-- **`NodeExec` restated over the circuit's own predicate** `NvHold`. -/
abbrev NodeExecV (R : Trace Fp → NodeRead K Dg Proof) (pubDig : List Fp → Dg) : Prop :=
  NodeExecH enc rdigest InnerAcc pvDig segStmt NvHold R pubDig

/-- **The tape component is discharged**: what remains of `NodeExecV` is SHA, the inner
verifiers, the asserts and the program's `PvD` layout (`TapeAt`). -/
theorem nodeExecV_of (R : Trace Fp → NodeRead K Dg Proof) (dec : List Fp → Dg)
    (h : ∀ tr pub, NvHold pub tr →
      NodeSha enc rdigest (R tr) ∧ NodeInner InnerAcc (R tr) ∧
        NodeAsserts enc pvDig segStmt (R tr) ∧ TapeAt dec tr (R tr)) :
    NodeExecV enc rdigest InnerAcc pvDig segStmt R (fun p => dec (pvDigest p)) := by
  intro tr pub hh
  obtain ⟨hS, hI, hA, hT⟩ := h tr pub hh
  exact ⟨hS, hI, nodeTape_of_hold dec (R tr) hh hT, hA⟩

/-- **`NvFaithful` for the node over the circuit's predicate.** -/
theorem nvFaithfulV_node [DecidableEq α] {Params : Type} (Acc : Stmt α → Proof → Prop)
    (hAcc : AccNative rdigest InnerAcc pvDig segStmt Acc) (R : Trace Fp → NodeRead K Dg Proof)
    (dec : List Fp → Dg) (par : Trace Fp → Params)
    (h : ∀ tr pub, NvHold pub tr →
      NodeSha enc rdigest (R tr) ∧ NodeInner InnerAcc (R tr) ∧
        NodeAsserts enc pvDig segStmt (R tr) ∧ TapeAt dec tr (R tr)) :
    NvFaithfulH NvHold (nodeDecode enc R (fun p => dec (pvDigest p)) par) (aggNodeV Acc rdigest) :=
  nvFaithfulH_node enc rdigest InnerAcc pvDig segStmt NvHold Acc hAcc R _ par
    (nodeExecV_of enc rdigest InnerAcc pvDig segStmt R dec h)

end Node

#print axioms nvConstr_of
#print axioms busEntries_mem
#print axioms memBalance_of
#print axioms busUsers_exported
#print axioms nodeTape_of_hold
#print axioms nodeExecV_of
#print axioms nvFaithfulV_node

end ZkFormal.PQ.NvField
