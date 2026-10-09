import ZkFormal.NearV3.Render.Node.Bytes

/-!
# ZkFormal.NearV3.Render.Node.WinFacts — facts about the hash windows of a record
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

/-- The windows of a record's fields. -/
theorem win_shape (v : NodeV3) (hw : v.wf) (w : Win) :
    (F.ch w ∈ fieldsOf v → w.look = false → w.pre = w.post) ∧
    (F.vh w ∈ fieldsOf v → w.look = tvOf v ∧ (twOf v = false → w.pre = w.post) ∧ w.slot = none) := by
  have hk : ∀ k ww l sl, (kidWin k ww l sl).look = false → (kidWin k ww l sl).pre = (kidWin k ww l sl).post := by
    intro k ww l sl h; cases k <;> simp_all [kidWin]
  have hv : ∀ s : NSlot3, s.wf → (valWin s).look = (match s with | .val .. => true | _ => false) ∧
      ((match s with | .val _ _ _ _ _ wr => wr | _ => false) = false → (valWin s).pre = (valWin s).post) ∧
      (valWin s).slot = none := by
    intro s hs
    cases s with
    | ref => exact ⟨rfl, fun _ => rfl, rfl⟩
    | val l i vl pre po wr =>
      refine ⟨rfl, fun h => ?_, rfl⟩
      simp only at h
      exact (hs.2.2.2.1 h).symm
  constructor
  · intro hf hl
    cases v with
    | leaf k sv m => simp [fieldsOf] at hf
    | ext k kid m =>
      simp [fieldsOf] at hf; subst hf; exact hk _ _ _ _ hl
    | branch sv kids m =>
      have : F.ch w ∈ branchWins kids := by cases sv <;> simpa [fieldsOf] using hf
      obtain ⟨k, ww, l, j, _, _, he⟩ := mem_branchWins this
      cases he; exact hk _ _ _ _ hl
  · intro hf
    cases v with
    | leaf k sv m =>
      simp [fieldsOf] at hf; subst hf
      have := hv sv hw.2.1
      refine ⟨by rw [this.1]; cases sv <;> rfl, fun h => this.2.1 (by cases sv <;> simp_all [twOf, NodeV3.value]), this.2.2⟩
    | ext k kid m => simp [fieldsOf] at hf
    | branch sv kids m =>
      cases sv with
      | none =>
        simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
        rcases hf with h | h | h | h
        · cases h
        · cases h
        · obtain ⟨_, _, _, _, _, _, he⟩ := mem_branchWins (by simpa using h); cases he
        · cases h
      | some s =>
        simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
        rcases hf with h | h | h | h | h | h
        · cases h
        · cases h
        · cases h
          have := hv s (hw.2.1 s rfl)
          refine ⟨by rw [this.1]; cases s <;> rfl, fun h => this.2.1 (by cases s <;> simp_all [twOf, NodeV3.value]),
            this.2.2⟩
        · cases h
        · obtain ⟨_, _, _, _, _, _, he⟩ := mem_branchWins (by simpa using h); cases he
        · cases h

/-- An element of the enumerated present children: its slot and its index. -/
theorem present_at : ∀ (Q : List NKid) (s : Nat) (L : List (NKid × Nat)),
    L = (Q.zip (List.range' s Q.length)).filter (fun (k, _) => k ≠ .none) →
    ∀ w k j, L[w]? = some (k, j) →
      s ≤ j ∧ j < s + Q.length ∧ Q.getD (j - s) .none = k ∧ k ≠ .none ∧ popK (Q.take (j - s)) = w
  | [], s, L, hP, w, k, j, h => by subst hP; simp at h
  | q :: Q, s, L, hP, w, k, j, h => by
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.filter_cons] at hP
    by_cases hq : q = .none
    · simp only [hq, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false] at hP
      have := present_at Q (s + 1) L hP w k j h
      refine ⟨by omega, by simp only [List.length_cons]; omega, ?_, this.2.2.2.1, ?_⟩
      · rw [show j - s = (j - (s + 1)) + 1 by omega, List.getD_cons_succ]; exact this.2.2.1
      · rw [show j - s = (j - (s + 1)) + 1 by omega, List.take_succ_cons]
        simp only [popK, List.filter_cons, hq, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
        exact this.2.2.2.2
    · simp only [hq, ne_eq, not_false_eq_true, decide_true, ite_true] at hP
      subst hP
      cases w with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [popK, hq]
      | succ w =>
        simp only [List.getElem?_cons_succ] at h
        have := present_at Q (s + 1) _ rfl w k j h
        refine ⟨by omega, by simp only [List.length_cons]; omega, ?_, this.2.2.2.1, ?_⟩
        · rw [show j - s = (j - (s + 1)) + 1 by omega, List.getD_cons_succ]; exact this.2.2.1
        · rw [show j - s = (j - (s + 1)) + 1 by omega, List.take_succ_cons]
          simp only [popK, List.filter_cons, hq, ne_eq, not_false_eq_true, decide_true, ite_true, List.length_cons]
          have := this.2.2.2.2; simp only [popK, ne_eq] at this ⊢; omega

theorem branch_win (kids : List NKid) (w : Win) (h : F.ch w ∈ branchWins kids) :
    ∃ j k, j < kids.length ∧ kids.getD j .none = k ∧ k ≠ .none ∧ w = kidWin k (popK (kids.take j))
      (popK (kids.take j) + 1 = popK kids) (some j) := by
  rw [branchWins_eq] at h
  unfold winsOf at h
  rw [List.mem_map] at h
  obtain ⟨⟨⟨k, j⟩, t⟩, hmem, he⟩ := h
  obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.1 hmem
  simp only [List.getElem_zip, List.getElem_range', Nat.zero_add, Prod.mk.injEq] at hx
  obtain ⟨hx1, rfl⟩ := hx
  have hP : (presentOf kids)[i]? = some (k, j) := by
    rw [List.getElem?_eq_getElem (by simpa using hi)]; rw [hx1]
  have := present_at kids 0 (presentOf kids) (by unfold presentOf; rw [List.range_eq_range']) i k j hP
  simp only [Nat.sub_zero, Nat.zero_add] at this
  obtain ⟨_, h2, h3, h4, h5⟩ := this
  refine ⟨j, k, by omega, h3, h4, ?_⟩
  simp only [F.ch.injEq] at he
  rw [← he, h5, popK_eq, Nat.one_mul]

theorem below_eq (kids : List NKid) (j : Nat) (hj : j ≤ kids.length) :
    ((List.range j).map fun i => bitOf (kidBitmap kids) i).sum = popK (kids.take j) := by
  rw [← sum_kbit (kids.take j) j (by simp; omega)]
  congr 1
  apply List.map_congr_left; intro i hi
  rw [bitOf_kidBitmap]
  have hi' := List.mem_range.1 hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi']

theorem kidWin_w (k : NKid) (w : Nat) (l : Bool) (s : Option Nat) :
    (kidWin k w l s).w = w ∧ (kidWin k w l s).lastw = l ∧ (kidWin k w l s).slot = s := by
  cases k <;> exact ⟨rfl, rfl, rfl⟩

/-- A child window: the extension's or a branch's. -/
theorem ch_facts (v : NodeV3) (w : Win) (hf : F.ch w ∈ fieldsOf v) (hw : v.wf) :
    ((typeOf v).2.1 = 1 ∧ (typeOf v).2.2.1 = 0 ∧ (typeOf v).2.2.2 = 0 ∧ w.w = 0 ∧ w.lastw = true ∧ w.slot = none) ∨
    ((typeOf v).2.1 = 0 ∧ (typeOf v).2.2.1 + (typeOf v).2.2.2 = 1 ∧ ∃ j0, j0 < 16 ∧ w.slot = some j0 ∧
      bitOf (bmvOf v) j0 = 1 ∧ w.w = ((List.range j0).map fun i => bitOf (bmvOf v) i).sum ∧
      (w.lastw = true ↔ w.w + 1 = ((List.range 16).map fun i => bitOf (bmvOf v) i).sum)) := by
  cases v with
  | leaf k sv m => simp [fieldsOf] at hf
  | ext k kid m =>
    simp [fieldsOf] at hf; subst hf
    left; have := kidWin_w kid 0 true none; exact ⟨rfl, rfl, rfl, this.1, this.2.1, this.2.2⟩
  | branch sv kids m =>
    right
    have hl : kids.length = 16 := hw.1
    have hb' : F.ch w ∈ branchWins kids := by cases sv <;> simpa [fieldsOf] using hf
    obtain ⟨j0, k, hj0, hk, hkn, rfl⟩ := branch_win kids w hb'
    have hbel := below_eq kids j0 (by omega)
    have hpop := below_eq kids 16 (by omega)
    rw [List.take_of_length_le (by omega)] at hpop
    have hkw := kidWin_w k (popK (kids.take j0)) (decide (popK (kids.take j0) + 1 = popK kids)) (some j0)
    simp only [bmvOf, isLE, Bool.false_eq_true, ite_false, kidsOf]
    refine ⟨by cases sv <;> rfl, by cases sv <;> rfl, j0, by omega, hkw.2.2, ?_, ?_, ?_⟩
    · rw [bitOf_kidBitmap, hk]; simp [kbit, hkn]
    · rw [hkw.1, hbel]
    · rw [hkw.2.1, hkw.1, hpop]; simp

end NodeGen3

end ZkFormal.NearV3.Render
