import ZkFormal.NearV3.Rcpt.Render.Srcp.RowDigest

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

def firstIndices : List Nat := [14, 15, 16, 51]

set_option maxRecDepth 4096 in
/-- The first root starts list zero, message zero, and SIZE at its receipt length. -/
theorem first_polynomials {bs : List SrcpB} (h : SrcpWf bs) (r : Nat)
    (D P : Nat → Int) (lst trn : Int) (n : Nat) (hn : n ∈ firstIndices) :
    ev (fun x => (cell bs r x : Int)) D (if r = 0 then 1 else 0) lst trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  have hp : 0 < bs.length := by have hh := h.nonempty; cases bs <;> simp_all
  have hj := h.j 0 hp
  have hq := h.q0 hp
  have hb : bs.getD 0 default = bs[0] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
  have hf := firstAt h
  simp only [List.getD_eq_getElem?_getD] at hf hb
  by_cases hr : r = 0
  · subst r
    simp only [firstIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn | hn | hn <;> subst n
    all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.c, Dsl.not,
      Dsl.k, SrcpV3.rt, SrcpV3.j, SrcpV3.q, SrcpV3.sz, SrcpV3.L,
      cell, R_pos h, rowFrame, firstAt h, frame, rootFrame, Frame.cell,
      before_zero, hf, hb, hj, hq, Int.add_right_neg]
  · simp only [firstIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn | hn | hn <;> subst n
    all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, hr]

theorem first_constraints {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (n : Nat) (hn : n ∈ firstIndices) :
    (SrcpV3.constraints.getD n (.const 0)).eval tr tt r pub = 0 := by
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => ((tr.cell tt ((r + 1) % tr.height tt) x).toNat : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [← ofNat_int, Fp.ofNat_toNat]
  · exact first_polynomials h r _ _ _ _ n hn

end ZkFormal.NearV3.Render.SrcpGen
