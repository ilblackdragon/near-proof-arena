import ZkFormal.NearV3.Rcpt.Render.Srcp.EndGate

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

def endIndices : List Nat := [50, 53, 54, 55]

set_option maxRecDepth 4096 in
/-- Padding and the terminal SIZE gate satisfy the actual transition polynomials. -/
theorem end_polynomials {bs : List SrcpB} (h : SrcpWf bs) (H r : Nat) (hr : r < H)
    (P : Nat → Int) (fst lst : Int) (n : Nat) (hn : n ∈ endIndices) :
    ev (fun x => (cell bs r x : Int)) (fun x => (cell bs ((r + 1) % H) x : Int))
      fst lst (if r + 1 = H then 0 else 1) P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  simp only [endIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with hn | hn | hn | hn <;> subst n
  · simpa [SrcpV3.constraints, ev, Dsl.mul3, Dsl.not, Dsl.sub, Dsl.c, Dsl.n, Dsl.k,
      SrcpV3.actE, Int.sub_eq_add_neg, Int.mul_assoc] using padding_next bs H r hr
  · simpa [SrcpV3.constraints, ev, Dsl.mul3, Dsl.not, Dsl.sub, Dsl.c, Dsl.n, Dsl.k,
      Int.sub_eq_add_neg, Int.mul_assoc] using end_gate_sl h r
  · simpa [SrcpV3.constraints, ev, Dsl.mul3, Dsl.not, Dsl.sub, Dsl.c, Dsl.n, Dsl.k,
      Int.sub_eq_add_neg, Int.mul_assoc] using end_gate_next bs H r hr
  · simpa [SrcpV3.constraints, ev, Dsl.mul3, Dsl.not, Dsl.sub, Dsl.c, Dsl.n, Dsl.k,
      Int.sub_eq_add_neg, Int.mul_assoc] using end_gate_continue bs H r hr

theorem end_constraints {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp} (hr : r < tr.height tt)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (hd : ∀ x, tr.cell tt ((r + 1) % tr.height tt) x =
      Fp.ofNat (cell bs ((r + 1) % tr.height tt) x))
    (n : Nat) (hn : n ∈ endIndices) :
    (SrcpV3.constraints.getD n (.const 0)).eval tr tt r pub = 0 := by
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => (cell bs ((r + 1) % tr.height tt) x : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [hd x, ofNat_int]
  · exact end_polynomials h _ r hr _ _ _ n hn

end ZkFormal.NearV3.Render.SrcpGen
