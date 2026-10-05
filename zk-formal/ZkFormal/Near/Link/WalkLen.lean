import ZkFormal.Near.Link.OutMain

/-!
# ZkFormal.Near.Link.WalkLen — the walk table is small (`KEYNIB` counting)

The walk table receives exactly as many `KEYNIB` messages as the receipt
table sends (`≤ 256·131`), and every walk has at least two steps, so the
total number of walk steps is below `p`.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem walkRecvs_keynib (ws : List WalkV) : walkRecvs ws B_KEYNIB =
    ws.flatMap fun w => (List.range (w.steps.length - 1)).map fun t =>
      [w.r, t, (w.edge (t + 1)).getD 2 0, if t + 2 = w.steps.length then 1 else 0] := by
  simp [walkRecvs, B_KEYNIB, B_EDGE]

theorem rcptSends_keynib (pub : List Fp) (rs : RcptVs) : rcptSends pub rs B_KEYNIB =
    (rs.zip (List.range rs.length)).flatMap fun p => (List.range p.1.keySyms.length).map fun t =>
      [p.2, t, p.1.keySyms.getD t 0, if t + 1 = p.1.keySyms.length then 1 else 0] := by
  simp [rcptSends, B_KEYNIB, B_BYTES]

theorem nib_length : ∀ (l : List Nat), (l.flatMap fun ch => [ch / 16, ch % 16]).length = 2 * l.length
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, List.length_append, nib_length l]; simp; omega

theorem keySyms_length (x : RcptV) : x.keySyms.length = 2 * x.v.length + 3 := by
  simp only [RcptV.keySyms, List.length_append, nib_length, List.length_cons, List.length_nil]
  omega

theorem steps_sum_le : ∀ (ws : List WalkV), (∀ w ∈ ws, 2 ≤ w.steps.length) →
    (ws.map fun w => w.steps.length).sum ≤ 2 * (ws.map fun w => w.steps.length - 1).sum
  | [], _ => by simp
  | w :: ws, h2 => by
    have := h2 w (by simp)
    have := steps_sum_le ws (fun w' hw' => h2 w' (by simp [hw']))
    simp; omega

theorem sum_le_mul {α : Type} (f : α → Nat) (B : Nat) : ∀ (l : List α), (∀ x ∈ l, f x ≤ B) →
    (l.map f).sum ≤ l.length * B
  | [], _ => by simp
  | a :: l, h => by
    have := sum_le_mul f B l (fun x hx => h x (by simp [hx]))
    have := h a (by simp)
    simp [Nat.succ_mul]; omega

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

/-- Total number of walk steps. -/
theorem walk_steps_lt : (ws.flatMap (·.steps)).length < P := by
  have hrl := rs_length_le h
  have hl := (perm h (b := B_KEYNIB) (by decide) (by decide)).length_eq
  rw [List.length_map, List.length_map, nearSends_keynib, nearRecvs_keynib, walkRecvs_keynib,
    rcptSends_keynib, List.length_flatMap, List.length_flatMap] at hl
  have hs : (((rs.zip (List.range rs.length)).map fun p => ((List.range p.1.keySyms.length).map
      fun t => [p.2, t, p.1.keySyms.getD t 0, if t + 1 = p.1.keySyms.length then 1 else 0]).length)).sum
      ≤ (rs.zip (List.range rs.length)).length * 131 := by
    apply sum_le_mul
    intro p hp
    obtain ⟨hr, hpe⟩ := mem_zip_range.mp (show (p.1, p.2) ∈ _ from hp)
    obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
    have := (idLens w).2.1
    simp only [List.length_map, List.length_range, keySyms_length]
    rw [← hpe]; omega
  have hz : (rs.zip (List.range rs.length)).length = rs.length := by simp
  rw [hz] at hs
  have h2 : ∀ w ∈ ws, 2 ≤ w.steps.length := fun w hw => (h.walk.steps w hw).1
  rw [List.length_flatMap]
  have : (ws.map fun w => w.steps.length).sum ≤ 2 * (ws.map fun w =>
      ((List.range (w.steps.length - 1)).map fun t =>
        [w.r, t, (w.edge (t + 1)).getD 2 0, if t + 2 = w.steps.length then 1 else 0]).length).sum := by
    simp only [List.length_map, List.length_range]
    exact steps_sum_le ws h2
  have : rs.length * 131 ≤ 256 * 131 := Nat.mul_le_mul_right _ hrl
  unfold P; omega

end Hyp

end Link

end ZkFormal.Near
