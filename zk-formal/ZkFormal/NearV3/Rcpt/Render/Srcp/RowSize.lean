import ZkFormal.NearV3.Rcpt.Render.Srcp.SizeStep

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

theorem rowCharge_int (bs : List SrcpB) (r : Nat) :
    (rowCharge bs r : Int) = (cell bs r SrcpV3.rt : Int) * (cell bs r SrcpV3.L : Int) +
      33 * ((cell bs r SrcpV3.sf : Int) * (cell bs r SrcpV3.sg : Int) *
        (1 - (cell bs r SrcpV3.lf : Int))) := by
  have hb := cell_bool_bound bs r SrcpV3.lf (by decide)
  have hl : cell bs r SrcpV3.lf = 0 ∨ cell bs r SrcpV3.lf = 1 := by omega
  rcases hl with hl | hl <;> simp [rowCharge, hl]

set_option maxRecDepth 4096 in
/-- The SIZE recurrence is valid as an integer identity, even beyond the field modulus. -/
theorem size_polynomial {bs : List SrcpB} (h : SrcpWf bs) (H r : Nat) (hr : r < H)
    (P : Nat → Int) (fst lst : Int) :
    ev (fun x => (cell bs r x : Int)) (fun x => (cell bs ((r + 1) % H) x : Int))
      fst lst (if r + 1 = H then 0 else 1) P
      (SrcpV3.constraints.getD 52 (.const 0)) = 0 := by
  by_cases hl : r + 1 = H
  · simp [SrcpV3.constraints, ev, hl]
  · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
    have he := congrArg (fun n : Nat => (n : Int)) (size_step h r)
    simp only [Int.natCast_add] at he
    rw [rowCharge_int] at he
    simp only [Int.sub_eq_add_neg] at he
    simp [SrcpV3.constraints, ev, Dsl.sub, Dsl.c, Dsl.n, Dsl.k, Dsl.not, Dsl.sum,
      Dsl.smul, Dsl.mul3, hm, hl]
    omega

theorem size_constraint {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp} (hr : r < tr.height tt)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (hd : ∀ x, tr.cell tt ((r + 1) % tr.height tt) x =
      Fp.ofNat (cell bs ((r + 1) % tr.height tt) x)) :
    (SrcpV3.constraints.getD 52 (.const 0)).eval tr tt r pub = 0 := by
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => (cell bs ((r + 1) % tr.height tt) x : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [hd x, ofNat_int]
  · exact size_polynomial h _ r hr _ _ _

end ZkFormal.NearV3.Render.SrcpGen
