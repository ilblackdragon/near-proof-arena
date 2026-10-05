import ZkFormal.Near.Render.Proof.WalkShape

/-!
# ZkFormal.Near.Render.Proof.WalkIdx — walks by index

Row `walkOff ws r + j` of the walk table is step `j` of walk `r`
(`stepsFrom_getD`); the table's rows decompose walk by walk
(`range_chunks_var`); per-walk index facts of a `Good` batch (`WalkIdx`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

theorem walkOff_succ (ws : List (List WStep)) (w : List WStep) (r : Nat) :
    walkOff (w :: ws) (r + 1) = w.length + walkOff ws r := by
  simp [walkOff, List.take_succ_cons]

theorem stepsFrom_getD : ∀ (ws : List (List WStep)) (r0 r j : Nat), r < ws.length → j < (ws.getD r []).length →
    (stepsFrom ws r0).getD (walkOff ws r + j) default = (r0 + r, (ws.getD r []).getD j default)
  | [], _, r, _, h, _ => absurd h (by simp)
  | w :: ws, r0, 0, j, _, hj => by
    simp only [List.getD_cons_zero] at hj
    simp only [stepsFrom, walkOff, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.getD_cons_zero]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj)]
    simp [List.getD_eq_getElem?_getD, hj]
  | w :: ws, r0, r + 1, j, hr, hj => by
    simp only [List.getD_cons_succ] at hj ⊢
    rw [walkOff_succ, stepsFrom, Nat.add_assoc, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD, stepsFrom_getD ws (r0 + 1) r j (by simpa using hr) hj]
    congr 1; omega

theorem range_chunks_var {β : Type} (f : Nat → List β) : ∀ (ws : List (List WStep)),
    (List.range (ws.map List.length).sum).flatMap f =
      (List.range ws.length).flatMap fun r => (List.range (ws.getD r []).length).flatMap fun j => f (walkOff ws r + j)
  | [] => by simp
  | w :: ws => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [List.range_add, List.flatMap_append, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.flatMap_map, range_chunks_var (fun q => f (w.length + q)) ws]
    congr 1
    · simp [walkOff]
    · apply flatMap_congr'; intro r _
      apply flatMap_congr'; intro j _
      simp only [List.getD_cons_succ, walkOff_succ, Nat.add_assoc]

/-- Index facts of one walk. -/
structure WalkIdx (w : List WStep) : Prop where
  len : 2 ≤ w.length
  first : (w.getD 0 default).t = none ∧ (w.getD 0 default).last = false
  ts : ∀ j, 1 ≤ j → j < w.length → (w.getD j default).t = some (j - 1)
  lasts : ∀ j, j < w.length → (w.getD j default).last = decide (j = w.length - 1)
  ok : ∀ j, j < w.length → StepOk (w.getD j default)

section
variable {c : Claim} {e : Ext} (hg : Good c e)
include hg

theorem walkIdx {r : Nat} (hr : r < e.rs.length) : WalkIdx ((walksOf (mkInfo c e)).getD r []) := by
  obtain ⟨rest, h1, h2, _⟩ := walk_of_index hg hr
  have hgood := walkGood_of hg hr
  rw [h1] at hgood ⊢
  obtain ⟨kd, kl⟩ := keySyms_facts hg (e.rc r)
  obtain ⟨l1, _, _, _, _, l6⟩ := walkFrom_shape _ _ _ _ h2 kd
  have hks : 1 ≤ (keySyms (e.rc r)).length := by simp [keySyms]
  have hend : ∀ j, j < (keySyms (e.rc r)).length →
      ((keySyms (e.rc r)).getD j 0 = SYM_END ↔ j = (keySyms (e.rc r)).length - 1) := by
    intro j hj
    constructor
    · intro h
      apply Classical.byContradiction; intro hne
      have hmem : (keySyms (e.rc r)).getD j 0 ∈ (keySyms (e.rc r)).dropLast := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        rw [List.mem_iff_getElem]
        exact ⟨j, by simp; omega, by simp [List.getElem_dropLast]⟩
      exact kd _ hmem h
    · intro h
      subst h
      rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, kl]; rfl
  refine ⟨by simp [l1]; omega, ⟨rfl, rfl⟩, ?_, ?_, fun j hj => hgood.ok _ ?_⟩
  · intro j hj1 hj2
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [List.getD_cons_succ, Nat.add_sub_cancel]
    have hj' : j' < rest.length := by simp at hj2; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some, (l6 j' hj').1]
    simp
  · intro j hj
    cases j with
    | zero => simp at hj ⊢; omega
    | succ j' =>
      simp only [List.getD_cons_succ, List.length_cons]
      have hj' : j' < rest.length := by simp at hj; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some, (l6 j' hj').2.2,
        decide_eq_decide, hend j' (by omega), l1]
      omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem _

end

end ZkFormal.Near.Render
