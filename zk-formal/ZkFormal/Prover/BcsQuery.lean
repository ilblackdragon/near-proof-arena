import ZkFormal.Prover.BcsShape
import ZkFormal.Stark.QueryBound

/-!
# ZkFormal.Prover.BcsQuery — the honest prover's unit query budget (P3)

`prover_unit : ProverQStmt`.  `WH(INIT)` (2 queries), one `WH` per slot (2), a
full MMCS tree per committed oracle (`2·2^n` leaf and `2·(2^n-1)` node queries,
`≤ 2^(n+2)`), and `numChunks` query answers.  Under `ProverWf` the oracles of
every message have the schedule's shapes (`BcsShape.inv_msg`, `msgShapes`), so
the tree depths are those of `schedOracles`.
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

theorem mapOC_qbp {α β : Type} (f : α → OracleComp hashSpec β) (c : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, QBP (fun _ => True) (f a) (c a)) →
      QBP (fun bs => bs.length = l.length) (mapOC f l) (l.map c).sum
  | [], _ => .pure _ _ rfl
  | a :: as, h => by
    simp only [mapOC, List.map_cons, List.sum_cons]
    refine QBP.bind (h a (by simp)) fun b _ => ?_
    refine QBP.bind_le (mapOC_qbp f c as fun x hx => h x (by simp [hx])) (fun bs hbs => ?_)
      (b := 0) (by omega)
    exact QBP.pure' 0 (by simp [hbs])

theorem sum_const {α : Type} (c : Nat) : ∀ l : List α, (l.map fun _ => c).sum = c * l.length
  | [] => by simp
  | _ :: l => by
    simp only [List.map_cons, List.sum_cons, sum_const c l, List.length_cons, Nat.mul_succ]; omega

theorem mapOC_qbp_const {α β : Type} (f : α → OracleComp hashSpec β) (c : Nat)
    (hf : ∀ a, QBP (fun _ => True) (f a) c) (l : List α) :
    QBP (fun bs => bs.length = l.length) (mapOC f l) (c * l.length) := by
  have h := mapOC_qbp f (fun _ => c) l fun a _ => hf a
  rw [sum_const] at h
  exact h

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

theorem buildTree_go_qbp (o : Oracle F) (n : Nat) :
    ∀ (k : Nat) (below : List Bytes) (acc : List (List Bytes)),
      QBP (fun _ => True) (buildTree.go (K := K) o n k below acc) (2 * (2 ^ k - 1))
  | 0, _, _ => .pure _ _ trivial
  | k + 1, below, acc => by
    simp only [buildTree.go]
    refine QBP.bind_le (mapOC_qbp_const _ 2 (fun _ => WH_qbp _ _) _)
      (fun lvl _ => buildTree_go_qbp o n k lvl _) ?_
    simp only [List.length_range, Nat.pow_succ]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

/-- A full MMCS tree of depth `n` costs at most `2^(n+2)` queries. -/
theorem buildTree_qbp (o : Oracle F) :
    QBP (fun _ => True) (buildTree (K := K) o) (2 ^ (treeLog (shapesOf o) + 2)) := by
  simp only [buildTree]
  refine QBP.bind_le (mapOC_qbp_const _ 2 (fun _ => WH_qbp _ _) _)
    (fun lv _ => buildTree_go_qbp _ _ _ _ _) ?_
  simp only [List.length_range, Nat.pow_succ]
  omega

/-- Cost of a list of oracle shapes. -/
def treeCost (os : List (List (Nat × Nat))) : Nat := (os.map fun m => 2 ^ (treeLog m + 2)).sum

theorem treeCost_append (a b : List (List (Nat × Nat))) :
    treeCost (a ++ b) = treeCost a + treeCost b := by
  simp [treeCost, List.sum_append]

theorem commitMsg_qbp (st : CState F K) (m : List (PartV K (Oracle F))) :
    QBP (fun st' => st'.τ = st.τ.push m) (commitMsg st m)
      (treeCost ((msgOracles m).map shapesOf) + 2) := by
  simp only [commitMsg]
  have e : treeCost ((msgOracles m).map shapesOf) =
      ((msgOracles m).map fun o => 2 ^ (treeLog (shapesOf o) + 2)).sum := by
    simp [treeCost, List.map_map, Function.comp_def]
  rw [e]
  refine QBP.bind (mapOC_qbp (buildTree (K := K)) (fun o => 2 ^ (treeLog (shapesOf o) + 2)) _
    fun o _ => buildTree_qbp o) fun lvs _ => ?_
  refine QBP.bind_le (WH_qbp _ _) (fun d' _ => QBP.pure' 0 rfl) (by omega)

/-- Cost of the remaining slots. -/
def slotsCost (ss : List Slot) : Nat := 2 * ss.length + treeCost (schedOracles ss)

variable {V : IopSpec F K} {pr : IopProver F K} {cb : Bytes}

theorem commitLoop_qbp (hw : ProverWf V pr cb) :
    ∀ (ss : List Slot) (st : CState F K), Inv V pr cb ss st.τ →
      QBP (fun _ => True) (commitLoop pr ss st) (slotsCost ss)
  | [], _, _ => .pure _ _ trivial
  | .msg parts :: ss, st, hi => by
    obtain ⟨hi', hf⟩ := inv_msg hw hi
    simp only [commitLoop]
    refine QBP.bind_le (commitMsg_qbp st _) (fun st' h' => ?_) (b := slotsCost ss) ?_
    · exact commitLoop_qbp hw ss st' (h' ▸ hi')
    · rw [msgShapes hf]
      simp only [slotsCost, schedOracles_msg, treeCost_append, List.length_cons]
      omega
  | .chal ood :: ss, st, hi => by
    simp only [commitLoop]
    refine QBP.bind_le (WH_qbp _ _) (fun d' _ => ?_) (b := slotsCost ss) ?_
    · exact commitLoop_qbp hw ss _ (inv_chal hw hi _)
    · simp only [slotsCost, schedOracles_chal, List.length_cons]
      omega

end

/-- **(P3)** The honest prover makes at most `proverQ V pr.hdr` oracle queries. -/
theorem prover_unit : ProverQStmt := by
  intro F K _ _ _ _ _ V pr pub cb hw
  simp only [proveTree, hw.hdrOk, ite_true]
  refine QBP.toQB (P := fun _ => True) ?_
  refine QBP.bind_le (WH_qbp _ _) (fun d0 _ => ?_) (b := slotsCost (V.schedule pr.hdr) +
    V.numChunks) ?_
  · refine QBP.bind (commitLoop_qbp hw _ _ inv_init) fun st _ => ?_
    exact QBP.bind_le (queryAnswers_qbp _ _) (fun _ _ => QBP.pure' 0 trivial) (by omega)
  · simp only [slotsCost, treeCost, proverQ]
    omega

end ZkFormal.Prover
