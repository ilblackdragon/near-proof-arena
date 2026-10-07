import ZkFormal.NearV3.Rcpt.Render.Srcp.RowListCarry
import ZkFormal.NearV3.Rcpt.Render.Srcp.RowRegisters

namespace ZkFormal.NearV3.Render.SrcpGen

theorem segment_gz (C : Frame) (g : Bool) (x : Nat) (hx : x ∈ SrcpV3.segConst) :
    ({ C with gz := g }).cell x = C.cell x := by
  simp only [SrcpV3.segConst, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx | hx <;> subst x <;> rfl

/-- Segment constants stay fixed until the leaf or path segment ends. -/
theorem internal_segment (B : SrcpB) (z : Nat) (a b : Kind)
    (hk : a ∈ kinds B) (hn : nextKind B a = some b) :
    (frame B z a).sg = false ∨ (frame B z a).sl = true ∨
      (∀ x ∈ SrcpV3.segConst, (frame B z b).cell x = (frame B z a).cell x) := by
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
      intro x hx
      simp only [SrcpV3.segConst, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx | hx <;> subst x <;> rfl
  | path i o =>
    have ho : o < 64 := (show i < B.path.length ∧ o < 64 by simpa using hh).2
    by_cases he : o = 63
    · right; left
      simp [frame, pathFrame, he]
    · right; right
      have ho' : o + 1 < 64 := by omega
      simp only [nextKind, ho', ite_true, Option.some.injEq] at hn
      subst b
      intro x hx
      simp only [SrcpV3.segConst, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx | hx <;> subst x <;> rfl

end ZkFormal.NearV3.Render.SrcpGen
