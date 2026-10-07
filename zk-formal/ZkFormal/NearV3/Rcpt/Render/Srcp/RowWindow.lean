import ZkFormal.NearV3.Rcpt.Render.Srcp.WindowBoundary

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

theorem row_window {bs : List SrcpB} (h : SrcpWf bs) (H r : Nat) (hH : R bs ≤ H)
    (P : Nat → Int) (fst lst trn : Int) (n : Nat) (hi : n ∈ windowStepIndices) :
    ev (fun x => (cell bs r x : Int)) (fun x => (cell bs ((r + 1) % H) x : Int))
      fst lst trn P (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  by_cases hr : r < R bs
  · by_cases hn : r + 1 < R bs
    · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hm]
      rcases adjAt hn with ⟨hk, he⟩ | ⟨hk, hd⟩
      · simp only [cell, hr, hn, ite_true, rowFrame]
        rw [he]
        exact window_step_polynomials _ _ _ _ _ _ (mem_recs (descriptor_mem hr)).2 hk
          P fst lst trn n hi
      · have hlast := none_last _ _ (mem_recs (descriptor_mem hr)).2 hk
        apply window_boundary _ _ P fst lst trn ?_ ?_ ?_ ?_ n hi
        · simp only [cell, hr, ite_true, rowFrame]
          rw [hlast]
          change (((frame _ _ (lastKind _)).rt).toNat : Int) = 0
          rw [terminal_rt]; rfl
        · simp only [cell, hr, ite_true, rowFrame]
          rw [hlast]
          change (((frame _ _ (lastKind _)).wl).toNat : Int) = 1
          rw [terminal_wl]; rfl
        · simp only [cell, hr, ite_true, rowFrame]
          rw [hlast]
          change (((frame _ _ (lastKind _)).sl).toNat : Int) = 1
          rw [terminal_sl]; rfl
        · simp only [cell, hn, ite_true, rowFrame]
          rw [hd]
          rfl
    · have he : r = R bs - 1 := by omega
      obtain ⟨hRt, _, hSl, _⟩ := last_cells h
      have hWl := last_wl_cell h
      have hSg := last_next_sg h H r hH hr hn
      apply window_boundary _ _ P fst lst trn ?_ ?_ ?_ ?_ n hi
      · simp [he, hRt]
      · simp [he, hWl]
      · simp [he, hSl]
      · simp [hSg]
  · have hp : R bs ≤ r := by omega
    apply window_padding _ _ P fst lst trn ?_ ?_ ?_ ?_ n hi
    all_goals simp [padding_cell hp, SrcpV3.rt, SrcpV3.sg, SrcpV3.wl, SrcpV3.sl, SrcpV3.sz]

theorem window_constraints {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp} (hH : R bs ≤ tr.height tt)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (hd : ∀ x, tr.cell tt ((r + 1) % tr.height tt) x =
      Fp.ofNat (cell bs ((r + 1) % tr.height tt) x))
    (n : Nat) (hi : n ∈ windowStepIndices) :
    (SrcpV3.constraints.getD n (.const 0)).eval tr tt r pub = 0 := by
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => (cell bs ((r + 1) % tr.height tt) x : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [hd x, ofNat_int]
  · exact row_window h _ r hH _ _ _ _ n hi

end ZkFormal.NearV3.Render.SrcpGen
