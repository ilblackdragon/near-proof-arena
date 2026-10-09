import ZkFormal.NearV3.Rcpt.Render.Srcp.RowSegment

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

set_option maxRecDepth 4096 in
/-- Duplicate source roots refer to the canonical empty receipt-list length. -/
theorem duplicate_frame (B : SrcpB) (z : Nat) (k : Kind) (g : Bool)
    (h : B.dup = true → B.L = 12) (D P : Nat → Int) (fst lst trn : Int) :
    ev (fun x => (({ frame B z k with gz := g }).cell x : Int)) D fst lst trn P
      (SrcpV3.constraints.getD 23 (.const 0)) = 0 := by
  cases k with
  | root =>
    cases hd : B.dup
    · simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.c, SrcpV3.rt, SrcpV3.dup,
        frame, rootFrame, Frame.cell, hd]
    · simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.c, Dsl.sub, Dsl.k,
        SrcpV3.rt, SrcpV3.dup, SrcpV3.L, frame, rootFrame, Frame.cell, hd, h hd]
  | leaf p =>
    simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.c, SrcpV3.rt, frame, leafFrame, Frame.cell]
  | path i o =>
    simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.c, SrcpV3.rt, frame, pathFrame, Frame.cell]

theorem row_duplicate {bs : List SrcpB} (h : SrcpWf bs) (r : Nat)
    (D P : Nat → Int) (fst lst trn : Int) :
    ev (fun x => (cell bs r x : Int)) D fst lst trn P
      (SrcpV3.constraints.getD 23 (.const 0)) = 0 := by
  by_cases hr : r < R bs
  · have hi := (mem_recs (descriptor_mem hr)).1
    have hB : bs.getD ((recs bs).getD r default).1 default ∈ bs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact List.getElem_mem _
    simp only [cell, hr, ite_true, rowFrame]
    exact duplicate_frame _ _ _ _ (h.dup _ hB) D P fst lst trn
  · have hp : R bs ≤ r := by omega
    simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.c, SrcpV3.rt, SrcpV3.sz, padding_cell hp]

theorem duplicate_constraint {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x)) :
    (SrcpV3.constraints.getD 23 (.const 0)).eval tr tt r pub = 0 := by
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => ((tr.cell tt ((r + 1) % tr.height tt) x).toNat : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [← ofNat_int, Fp.ofNat_toNat]
  · exact row_duplicate h r _ _ _ _ _

end ZkFormal.NearV3.Render.SrcpGen
