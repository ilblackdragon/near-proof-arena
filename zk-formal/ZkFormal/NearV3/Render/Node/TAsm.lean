import ZkFormal.NearV3.Render.Node.TRow

/-!
# ZkFormal.NearV3.Render.Node.TAsm — the table's messages, record by record
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

/-- Messages of the rows of record `n`. -/
def recN (vs : List NodeS3) (n b : Nat) (sd : Bool) : List ZkFormal.Near.Msg :=
  (List.range (layN vs n).length).flatMap fun p => rowN (rowCell vs (mkR vs n p)) b sd

theorem zip_flatMap {β : Type} (vs : List NodeS3) (F' : NodeS3 × Nat → List β) :
    (vs.zip (List.range vs.length)).flatMap F' = (List.range vs.length).flatMap fun n => F' (rec vs n, n) := by
  have : vs.zip (List.range vs.length) = (List.range vs.length).map fun n => (rec vs n, n) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp at h1
    simp [rec, List.getD_eq_getElem?_getD, h1]
  rw [this, List.flatMap_map]

theorem zip_map {β : Type} (vs : List NodeS3) (F' : NodeS3 × Nat → β) :
    (vs.zip (List.range vs.length)).map F' = (List.range vs.length).flatMap fun n => [F' (rec vs n, n)] := by
  rw [← zip_flatMap (F' := fun x => [F' x])]
  induction (vs.zip (List.range vs.length)) <;> simp_all

theorem zip_filterMap {β : Type} (vs : List NodeS3) (F' : NodeS3 × Nat → Option β) :
    (vs.zip (List.range vs.length)).filterMap F' =
      (List.range vs.length).flatMap fun n => (F' (rec vs n, n)).toList := by
  rw [← zip_flatMap (F' := fun x => (F' x).toList)]
  induction (vs.zip (List.range vs.length)) with
  | nil => rfl
  | cons x l ih => cases h : F' x <;> simp_all [List.filterMap_cons]

/-- The node rows' messages, record by record. -/
theorem nodes_flat (vs : List NodeS3) (b : Nat) (sd : Bool) :
    (List.range (R vs)).flatMap (fun q => rowN (rowCell vs ((recsOf vs).getD q default)) b sd) =
      (List.range vs.length).flatMap fun n => recN vs n b sd := by
  rw [show R vs = (recsOf vs).length from rfl,
    ← ZkFormal.Near.Render.flatMap_getD default (recsOf vs) (fun r => rowN (rowCell vs r) b sd)]
  simp only [recsOf, List.flatMap_assoc, recN, nodeRecs, List.flatMap_map]

theorem gt_zero (m : ZkFormal.Near.Msg) : gt 0 m = [] := rfl
theorem gt_one (m : ZkFormal.Near.Msg) : gt 1 m = [m] := rfl

theorem rowN_pad (vs : List NodeS3) (b : Nat) (sd : Bool) : rowN (padCell (total vs)) b sd = [] := by
  simp [rowN, rowN0, rowNU, padCell, gt]

theorem rowN_sum (vs : List NodeS3) (b : Nat) (sd : Bool) :
    rowN (sumCell (total vs)) b sd = if b = B_SIZE ∧ sd = true then [[0, total vs]] else [] := by
  by_cases h : b = B_SIZE ∧ sd = true
  · obtain ⟨rfl, rfl⟩ := h; simp [rowN, rowN0, rowNU, sumCell, gt, B_SIZE, B_BYTES, B_DIGEST, B_PARENT, B_VPARENT, B_EDGE,
      B_BMAP, B_DIGS, B_DUP, B_ENT, B_UPB]
  · rw [if_neg h]; simp only [rowN, rowN0, rowNU, sumCell, gt]
    simp only [Nat.reduceEqDiff, ite_false, ite_true]
    by_cases h2 : B_SIZE = b ∧ true = sd
    · exact absurd ⟨h2.1.symm, h2.2.symm⟩ h
    · simp [h2]
      intro h3; cases sd <;> simp_all

end NodeGen3

end ZkFormal.NearV3.Render
