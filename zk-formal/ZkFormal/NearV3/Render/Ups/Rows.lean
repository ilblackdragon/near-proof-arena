import ZkFormal.NearV3.Render.Ups.Frame

/-!
# ZkFormal.NearV3.Render.Ups.Rows — rows of the honest table

`groupOk_of`: a group of constraints holds on every row once it holds on every active row
`q < R` with its successor (the next record, or the zero row after the last record); the
padding rows are `pad_all` / `pad_last`.  `actCase`: an active row is a walk, value or node
row of an instance, and its successor is `nextRK` of it, the next instance's `W0`, or zero.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI

namespace UpsGen

variable {insts : List UpsInst}

theorem getD_mem {q : Nat} (h : q < R insts) : (recs insts).getD q default ∈ recs insts := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem _

theorem adjAt (hs : UpsShape insts) {q : Nat} (h : q + 1 < R insts) :
    RAdj insts ((recs insts).getD q default) ((recs insts).getD (q + 1) default) := by
  have := (recs_adj hs).get q h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by unfold R at h; omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact this

theorem inst_mem {i : Nat} (hi : i < insts.length) : inst insts i ∈ insts := by
  simp only [inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem recs_last (hs : UpsShape insts) :
    (recs insts).getLast? = some (insts.length - 1, lastRK (inst insts (insts.length - 1))) := by
  unfold recs
  obtain ⟨m, hm⟩ : ∃ m, insts.length = m + 1 := ⟨insts.length - 1, by have := hs.pos; omega⟩
  have hI := inst_mem (insts := insts) (i := m) (by omega)
  rw [hm, List.range_succ, List.flatMap_append, List.getLast?_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getLast?_map]
  rw [show insts.getD m default = inst insts m from rfl, recsI_last (hs.L1 _ hI) (hs.nQ1 _ hI) (hs.q1 _ hI)]
  simp

theorem R_pos (hs : UpsShape insts) : 0 < R insts := by
  have := recs_last hs
  unfold R
  cases h : recs insts with
  | nil => rw [h] at this; simp at this
  | cons _ _ => simp

theorem lastAt (hs : UpsShape insts) :
    (recs insts).getD (R insts - 1) default = (insts.length - 1, lastRK (inst insts (insts.length - 1))) := by
  have h := recs_last hs
  rw [List.getLast?_eq_getElem?] at h
  rw [List.getD_eq_getElem?_getD]
  unfold R; rw [h]; rfl

theorem firstAt (hs : UpsShape insts) : (recs insts).getD 0 default = (0, RK.w 0) := by
  unfold recs
  obtain ⟨m, hm⟩ : ∃ m, insts.length = m + 1 := ⟨insts.length - 1, by have := hs.pos; omega⟩
  rw [hm, List.range_succ_eq_map]
  simp [recsI, List.range_succ_eq_map]

/-- The successor cells of an active row. -/
def nextCell (insts : List UpsInst) (q x : Nat) : Int :=
  if q + 1 < R insts then rowCell insts (q + 1) ((recs insts).getD (q + 1) default) x else 0

theorem groupOk_of (hs : UpsShape insts) {H : Nat} (hH : R insts + 1 ≤ H) {es : List Expr}
    (hsub : ∀ e ∈ es, e ∈ UpsV3.constraints)
    (hact : ∀ q, q < R insts → ∀ (C D P : Nat → Int),
      (∀ x, x < 200 → C x = rowCell insts q ((recs insts).getD q default) x) →
      (∀ x, x < 200 → D x = nextCell insts q x) →
      ∀ ex ∈ es, ((ev C D (if q = 0 then 1 else 0) 0 1 P ex : Int) : Fp) = 0) :
    GroupOk insts H es := by
  intro q hq C D P hC hD ex hex
  by_cases ha : q < R insts
  · have h1 : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt (by omega)
    rw [if_neg (show q + 1 ≠ H by omega), if_neg (show q + 1 ≠ H by omega)]
    apply hact q ha C D P (fun x hx => by rw [hC x hx]; simp [cell, ha]) (fun x hx => by
      rw [hD x hx, h1]; simp only [cell, nextCell]) ex hex
  · have hpz : ∀ x, x < 200 → C x = 0 := fun x hx => by rw [hC x hx]; simp [cell, ha]
    have hq0 : q ≠ 0 := by have := R_pos hs; omega
    rw [if_neg hq0]
    have he := hsub ex hex
    by_cases hl : q + 1 = H
    · rw [if_pos hl, if_pos hl]
      have hz := List.all_eq_true.1 pad_last ex he
      rw [ev_vz (zc := fun x => decide (x < 200)) (zn := fun x => x == 113) (zf := true) (zl := false) (zt := true)
        (fun x h => hpz x (by simpa using h)) (fun x h => ?_) (fun _ => rfl) (fun h => absurd h (by decide))
        (fun _ => rfl) ex hz]
      · rfl
      · simp only [beq_iff_eq] at h; subst h
        rw [hD 113 (by decide), hl, Nat.mod_self]
        simp only [cell, R_pos hs, if_true, firstAt hs, rowCell]
        rfl
    · rw [if_neg hl, if_neg hl]
      have hz := List.all_eq_true.1 pad_all ex he
      rw [ev_vz (zc := fun x => decide (x < 200)) (zn := fun x => decide (x < 200)) (zf := true) (zl := false)
        (zt := false) (fun x h => hpz x (by simpa using h)) (fun x h => ?_) (fun _ => rfl)
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) ex hz]
      · rfl
      · simp only [decide_eq_true_eq] at h
        rw [hD x h, Nat.mod_eq_of_lt (by omega)]
        simp [cell, show ¬ q + 1 < R insts by omega]

end UpsGen

end ZkFormal.NearV3.Render
