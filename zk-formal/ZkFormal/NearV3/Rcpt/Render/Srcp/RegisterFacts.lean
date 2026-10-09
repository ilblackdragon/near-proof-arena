import ZkFormal.NearV3.Rcpt.Render.Srcp.TransitionFacts

namespace ZkFormal.NearV3.Render.SrcpGen

theorem Frame.reg_cell (C : Frame) (x : Nat) (hx : x < 32) :
    C.cell (SrcpV3.reg x) = C.regs.getD x 0 := by
  simp [SrcpV3.reg, Nat.add_comm 22 x, Frame.cell, hx]

theorem terminal_wl (B : SrcpB) (z : Nat) : (frame B z (lastKind B)).wl = true := by
  by_cases hp : B.path.length = 0 <;> simp [lastKind, hp, frame, leafFrame, pathFrame]

/-- Every internal successor either has its shift gate disabled or shifts all registers. -/
theorem internal_registers (B : SrcpB) (z : Nat) (a b : Kind)
    (hk : a ∈ kinds B) (hn : nextKind B a = some b) :
    (frame B z a).sg = false ∨ (frame B z a).wl = true ∨
      (∀ x, (frame B z b).regs.getD x 0 = (frame B z a).regs.getD (x + 1) 0) := by
  have hh := (mem_kinds B a).mp hk
  cases a with
  | root => exact Or.inl rfl
  | leaf p =>
    have hp : p < 32 := by simpa using hh
    by_cases he : p = 31
    · right; left
      simp [frame, leafFrame, he]
    · right; right
      have hp' : p + 1 < 32 := by omega
      simp only [nextKind, hp', ite_true, Option.some.injEq] at hn
      subst b
      exact leaf_shift B z p
  | path i o =>
    have ho : o < 64 := (show i < B.path.length ∧ o < 64 by simpa using hh).2
    by_cases he : o % 32 = 31
    · right; left
      simp [frame, pathFrame, he]
    · right; right
      have ho' : o + 1 < 64 := by omega
      simp only [nextKind, ho', ite_true, Option.some.injEq] at hn
      subst b
      intro x
      exact path_shift B z i o x ho he

end ZkFormal.NearV3.Render.SrcpGen
