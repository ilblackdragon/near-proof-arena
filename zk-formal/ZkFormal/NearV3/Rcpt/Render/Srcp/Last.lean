import ZkFormal.NearV3.Rcpt.Render.Srcp.First

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

theorem terminal_rt (B : SrcpB) (z : Nat) : (frame B z (lastKind B)).rt = false := by
  by_cases hp : B.path.length = 0 <;> simp [lastKind, hp, frame, leafFrame, pathFrame]

theorem terminal_sg (B : SrcpB) (z : Nat) : (frame B z (lastKind B)).sg = true := by
  by_cases hp : B.path.length = 0 <;> simp [lastKind, hp, frame, leafFrame, pathFrame]

theorem terminal_sl (B : SrcpB) (z : Nat) : (frame B z (lastKind B)).sl = true := by
  by_cases hp : B.path.length = 0 <;> simp [lastKind, hp, frame, leafFrame, pathFrame]

/-- Last active row is a complete segment end and the unique SIZE sender. -/
theorem last_cells {bs : List SrcpB} (h : SrcpWf bs) :
    cell bs (R bs - 1) SrcpV3.rt = 0 ∧
    cell bs (R bs - 1) SrcpV3.sg = 1 ∧
    cell bs (R bs - 1) SrcpV3.sl = 1 ∧
    cell bs (R bs - 1) SrcpV3.gz = 1 := by
  have hp := R_pos h
  have hr : R bs - 1 < R bs := by omega
  have he : R bs - 1 + 1 = R bs := by omega
  simp only [cell, hr, ite_true, lastAt h, rowFrame]
  simp [SrcpV3.rt, SrcpV3.sg, SrcpV3.sl, SrcpV3.gz, Frame.cell,
    terminal_rt, terminal_sg, terminal_sl, he]

def lastIndices : List Nat := [17, 18, 56]

set_option maxRecDepth 4096 in
/-- A physically full source table may end on its last segment; padding is optional. -/
theorem last_polynomials {bs : List SrcpB} (h : SrcpWf bs) (H r : Nat)
    (hH : R bs ≤ H) (hr : r < H) (D P : Nat → Int) (fst trn : Int)
    (n : Nat) (hn : n ∈ lastIndices) :
    ev (fun x => (cell bs r x : Int)) D fst (if r + 1 = H then 1 else 0) trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  by_cases he : r + 1 = H
  · by_cases ha : r < R bs
    · have he' : r = R bs - 1 := by omega
      subst r
      obtain ⟨hRt, hSg, hSl, hGz⟩ := last_cells h
      simp only [SrcpV3.rt, SrcpV3.sg, SrcpV3.sl, SrcpV3.gz] at hRt hSg hSl hGz
      simp only [lastIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with hn | hn | hn <;> subst n
      all_goals simp [SrcpV3.constraints, ev, Dsl.c, Dsl.not, Dsl.sub, Dsl.k,
        SrcpV3.rt, SrcpV3.sg, SrcpV3.sl, SrcpV3.gz, hRt, hSg, hSl, hGz, he]
    · have hp : R bs ≤ r := by omega
      simp only [lastIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with hn | hn | hn <;> subst n
      all_goals simp [SrcpV3.constraints, ev, Dsl.c, Dsl.not, Dsl.sub, Dsl.k,
        SrcpV3.rt, SrcpV3.sg, SrcpV3.sl, SrcpV3.gz, SrcpV3.sz, padding_cell hp, he]
  · simp only [lastIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn | hn <;> subst n
    all_goals simp [SrcpV3.constraints, ev, he]

theorem last_constraints {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp} (hH : R bs ≤ tr.height tt) (hr : r < tr.height tt)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (n : Nat) (hn : n ∈ lastIndices) :
    (SrcpV3.constraints.getD n (.const 0)).eval tr tt r pub = 0 := by
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => ((tr.cell tt ((r + 1) % tr.height tt) x).toNat : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [← ofNat_int, Fp.ofNat_toNat]
  · exact last_polynomials h _ r hH hr _ _ _ _ n hn

end ZkFormal.NearV3.Render.SrcpGen
