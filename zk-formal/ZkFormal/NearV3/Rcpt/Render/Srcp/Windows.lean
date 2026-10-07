import ZkFormal.NearV3.Rcpt.Render.Srcp.Facts

namespace ZkFormal.NearV3.Render.SrcpGen

/-- Two-window decomposition fixes path flags even at the 31/32 boundary. -/
theorem path_window (o : Nat) (ho : o < 64) :
    o % 32 < 32 ∧
    (o = 0 ↔ o % 32 = 0 ∧ ¬ 32 ≤ o) ∧
    (o = 63 ↔ o % 32 = 31 ∧ 32 ≤ o) ∧
    (o % 32 ≠ 31 → (o + 1) % 32 = o % 32 + 1 ∧
      (32 ≤ o + 1 ↔ 32 ≤ o)) := by omega

theorem leaf_window (B : SrcpB) (z p : Nat) (hp : p < 32) :
    (leafFrame B z p).pw < 32 ∧
    (leafFrame B z p).sf = (leafFrame B z p).wf ∧
    (leafFrame B z p).sl = (leafFrame B z p).wl ∧
    (leafFrame B z p).wn = false := by
  exact ⟨hp, rfl, rfl, rfl⟩

theorem path_first_flag (B : SrcpB) (z i o : Nat) (ho : o < 64) :
    (pathFrame B z i o).sf =
      ((pathFrame B z i o).wf && !(pathFrame B z i o).wn) := by
  by_cases hw : o % 32 = 0 <;> by_cases hn : 32 ≤ o
  all_goals
    have hz : (o = 0) = (o % 32 = 0 ∧ ¬ 32 ≤ o) :=
      propext (path_window o ho).2.1
    simp [pathFrame, hz, hw, hn]

theorem path_last_flag (B : SrcpB) (z i o : Nat) (ho : o < 64) :
    (pathFrame B z i o).sl =
      ((pathFrame B z i o).wl && (pathFrame B z i o).wn) := by
  by_cases hw : o % 32 = 31 <;> by_cases hn : 32 ≤ o
  all_goals
    have hz : (o = 63) = (o % 32 = 31 ∧ 32 ≤ o) :=
      propext (path_window o ho).2.2.1
    simp [pathFrame, hz, hw, hn]

/-- All shifted registers agree across adjacent rows inside a leaf window. -/
theorem leaf_shift (B : SrcpB) (z p x : Nat) :
    (leafFrame B z (p + 1)).regs.getD x 0 =
      (leafFrame B z p).regs.getD (x + 1) 0 := by
  simp only [leaf_registers]
  congr 1
  omega

/-- Path registers reset only at a window boundary. -/
theorem path_shift (B : SrcpB) (z i o x : Nat)
    (ho : o < 64) (hw : o % 32 ≠ 31) :
    (pathFrame B z i (o + 1)).regs.getD x 0 =
      (pathFrame B z i o).regs.getD (x + 1) 0 := by
  simp only [path_registers]
  congr 1
  have := (path_window o ho).2.2.2 hw
  omega

end ZkFormal.NearV3.Render.SrcpGen
