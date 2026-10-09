import ZkFormal.NearV3.Rcpt.Render.Srcp.SegmentCarry

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

def segmentPolys : List Expr := SrcpV3.segConst.map fun x =>
  Dsl.mul3 (Dsl.c SrcpV3.sg) (Dsl.not (Dsl.c SrcpV3.sl))
    (Dsl.sub (Dsl.n x) (Dsl.c x))

theorem segmentPolys_eq : (SrcpV3.constraints.drop 77).take 4 = segmentPolys := rfl

theorem row_segment {bs : List SrcpB} (h : SrcpWf bs) (H r : Nat)
    (hH : R bs ≤ H) (P : Nat → Int) (fst lst trn : Int) :
    ∀ ex ∈ segmentPolys,
      ev (fun x => (cell bs r x : Int)) (fun x => (cell bs ((r + 1) % H) x : Int))
        fst lst trn P ex = 0 := by
  intro ex hex
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hex
  by_cases hr : r < R bs
  · rcases segment_carry_cases h H r hH hr with hSg | hWl | hReg
    · simp [ev, Dsl.mul3, Dsl.c, Dsl.n, Dsl.not, Dsl.sub, Dsl.k, hSg]
    · simp [ev, Dsl.mul3, Dsl.c, Dsl.n, Dsl.not, Dsl.sub, Dsl.k, hWl]
    · simp [ev, Dsl.mul3, Dsl.c, Dsl.n, Dsl.not, Dsl.sub, Dsl.k, hReg x hx, Int.add_right_neg]
  · have hp : R bs ≤ r := by omega
    simp [ev, Dsl.mul3, Dsl.c, Dsl.n, Dsl.not, Dsl.sub, Dsl.k,
      padding_cell hp, SrcpV3.sg, SrcpV3.sz]

theorem segment_constraints {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp} (hH : R bs ≤ tr.height tt)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (hd : ∀ x, tr.cell tt ((r + 1) % tr.height tt) x =
      Fp.ofNat (cell bs ((r + 1) % tr.height tt) x)) :
    ∀ ex ∈ (SrcpV3.constraints.drop 77).take 4, ex.eval tr tt r pub = 0 := by
  rw [segmentPolys_eq]
  intro ex hex
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => (cell bs ((r + 1) % tr.height tt) x : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [hd x, ofNat_int]
  · exact row_segment h _ r hH _ _ _ _ ex hex

end ZkFormal.NearV3.Render.SrcpGen
