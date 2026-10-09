import ZkFormal.NearV3.Rcpt.Render.Srcp.Local

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

/-- Padding carries SIZE while all shape columns are zero. -/
theorem padding_shape (bs : List SrcpB) (r : Nat) (hr : R bs ≤ r)
    (D P : Nat → Int) (fst lst trn : Int) (n : Nat) (hn : n ∈ shapeIndices) :
    ev (fun x => (cell bs r x : Int)) D fst lst trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  simp only [shapeIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst n
  all_goals simp [padding_cell hr, SrcpV3.constraints, ev, Dsl.bool, Dsl.mul3,
    Dsl.sub, Dsl.not, Dsl.c, Dsl.k, Dsl.smul,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.dir, SrcpV3.aw, SrcpV3.sz]

/-- Every rendered row satisfies the selected shape equations over the integers. -/
theorem row_shape (bs : List SrcpB) (r : Nat)
    (D P : Nat → Int) (fst lst trn : Int) (n : Nat) (hn : n ∈ shapeIndices) :
    ev (fun x => (cell bs r x : Int)) D fst lst trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  by_cases hr : r < R bs
  · exact active_shape bs r hr D P fst lst trn n hn
  · exact padding_shape bs r (by omega) D P fst lst trn n hn

/-- Integer shape proofs discharge the actual field-valued table polynomials. -/
theorem shape_constraints {bs : List SrcpB} {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (n : Nat) (hn : n ∈ shapeIndices) :
    (SrcpV3.constraints.getD n (.const 0)).eval tr tt r pub = 0 := by
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => ((tr.cell tt ((r + 1) % tr.height tt) x).toNat : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [← ofNat_int, Fp.ofNat_toNat]
  · exact row_shape bs r _ _ _ _ _ n hn

end ZkFormal.NearV3.Render.SrcpGen
