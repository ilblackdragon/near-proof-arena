import ZkFormal.NearV3.Rcpt.Render.Srcp.RowEnd

namespace ZkFormal.NearV3.Render.SrcpGen

/-- A valid descriptor has no internal successor exactly at its list's last row. -/
theorem none_last (B : SrcpB) (k : Kind) (hk : k ∈ kinds B)
    (hn : nextKind B k = none) : k = lastKind B := by
  have hh := (mem_kinds B k).mp hk
  cases k with
  | root => simp [nextKind] at hn
  | leaf p =>
    have hp : p < 32 := by simpa using hh
    have hp31 : p = 31 := by
      by_cases ha : p + 1 < 32
      · simp [nextKind, ha] at hn
      · omega
    subst p
    have hz : B.path.length = 0 := by
      by_cases ha : 0 < B.path.length
      · simp [nextKind, ha] at hn
      · omega
    simp [lastKind, hz]
  | path i o =>
    have hh' : i < B.path.length ∧ o < 64 := by simpa using hh
    have ho : o = 63 := by
      by_cases ha : o + 1 < 64
      · simp [nextKind, ha] at hn
      · omega
    subst o
    have hi : i = B.path.length - 1 := by
      by_cases ha : i + 1 < B.path.length
      · simp [nextKind, ha] at hn
      · omega
    simp [lastKind, hi, show B.path.length ≠ 0 by omega]

/-- Every row kind carries the same list-level constants. -/
theorem list_constant (B : SrcpB) (z : Nat) (k : Kind) (g : Bool)
    (x : Nat) (hx : x ∈ SrcpV3.listConst) :
    ({ frame B z k with gz := g }).cell x = (rootFrame B z).cell x := by
  simp only [SrcpV3.listConst, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx | hx <;> subst x
  all_goals cases k <;> rfl

/-- Valid active row descriptors in the generated table. -/
theorem descriptor_mem {bs : List SrcpB} {r : Nat} (hr : r < R bs) :
    (recs bs).getD r default ∈ recs bs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
  exact List.getElem_mem _

theorem first_sg {bs : List SrcpB} (h : SrcpWf bs) : cell bs 0 SrcpV3.sg = 0 := by
  simp only [cell, R_pos h, ite_true, firstAt h, rowFrame]
  rfl

end ZkFormal.NearV3.Render.SrcpGen
