import ZkFormal.Near.Extract.RcptBytes

/-!
# ZkFormal.Near.Extract.RcptGates — states and gates on the rows of a receipt

On row `s + j` of a receipt: the field state (`cell_state`), `rl` (only the
last row), `rf` (only the first), `kz` (the first two `VL` rows), `gDg`
(`XRI`/`XLH` starts), `gKA`.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem nodup_map_inj {α β : Type} (g : α → β) :
    ∀ (l : List α), (l.map g).Nodup → ∀ a ∈ l, ∀ b ∈ l, g a = g b → a = b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro hnd a ha b hb he
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · rw [h1, h2]
    · subst h1; exact absurd ⟨b, h2, he.symm⟩ hnd.1
    · subst h2; exact absurd ⟨a, h1, he⟩ hnd.1
    · exact ih hnd.2 a h1 b h2 he

theorem plan_nodup (h : Bool) (Lp Lv Ls kt : Nat) : ((plan h Lp Lv Ls kt).map (·.1)).Nodup := by
  cases h <;> simp only [plan, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil] <;> decide

theorem plan_states (h : Bool) (Lp Lv Ls kt : Nat) : ∀ f ∈ plan h Lp Lv Ls kt, f.1 ∈ states ∧ f.1 ≠ sCL := by
  intro f hf
  have : f.1 ∈ (plan h Lp Lv Ls kt).map (·.1) := List.mem_map_of_mem hf
  revert this; generalize f.1 = X
  cases h <;> simp only [plan, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil] <;> intro hX <;> revert X <;> decide

theorem plan_cover (h : Bool) (Lp Lv Ls kt j : Nat) (hj : j < total h Lp Lv Ls kt) :
    ∃ f ∈ plan h Lp Lv Ls kt, f.2.1 ≤ j ∧ j < f.2.1 + f.2.2 := by
  have hm : j ∈ List.range' 0 (total h Lp Lv Ls kt) := by simp [List.mem_range']; omega
  rw [range'_plan] at hm
  obtain ⟨p, hp, hjp⟩ := List.mem_flatMap.mp hm
  simp only [planSegs, List.mem_map] at hp
  obtain ⟨f, hf, rfl⟩ := hp
  simp [List.mem_range'] at hjp
  exact ⟨f, hf, by omega, by omega⟩

/-- Which field ends the receipt. -/
theorem plan_last (h : Bool) (Lp Lv Ls kt : Nat) : ∀ f ∈ plan h Lp Lv Ls kt,
    (f.1 = sXRZ ∨ (f.1 = sXLH ∧ h = false)) ↔ f.2.1 + f.2.2 = total h Lp Lv Ls kt := by
  intro f hf
  cases h
  · simp only [plan, hN, Bool.false_eq_true, if_false, List.append_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp [total, Vt, sXRZ, sXLH, sPL, sP, sVL, sV, sRID, sT0, sSL, sS, sKT, sPK, sGP, sTL, sDEP, sXP0, sXG,
        sXST, sXL0] <;> omega
  · simp only [plan, hN, if_true, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;>
      simp [total, Vt, sXRZ, sXLH, sPL, sP, sVL, sV, sRID, sT0, sSL, sS, sKT, sPK, sGP, sTL, sDEP, sXP0, sXG,
        sXST, sXL0, sXRI, sXRH, sXRF] <;> omega

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- **The state of each receipt row.** -/
theorem cell_state {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt)
    {X off L : Nat} (hm : (X, off, L) ∈ plan h Lp Lv Ls kt) (j : Nat) (hj : j < total h Lp Lv Ls kt) :
    tr.cell T_RCPT (s + j) X = if off ≤ j ∧ j < off + L then 1 else 0 := by
  have hfin := lay.fin
  split
  · rename_i hin
    have := (lay.flds _ hm).fld.st (j - off) (by simp; omega)
    simpa [show s + off + (j - off) = s + j by omega] using this
  · rename_i hin
    obtain ⟨f, hf, h1, h2⟩ := plan_cover h Lp Lv Ls kt j hj
    have F := lay.flds f hf
    have hst := F.fld.st (j - f.2.1) (by omega)
    rw [show s + f.2.1 + (j - f.2.1) = s + j by omega] at hst
    have hne : f.1 ≠ X := by
      intro he
      have := nodup_map_inj (·.1) _ (plan_nodup h Lp Lv Ls kt) f hf _ hm he
      subst this; exact hin ⟨h1, h2⟩
    exact (oneHot hL (by omega) (plan_states h Lp Lv Ls kt f hf).1 hst).2 X
      (plan_states h Lp Lv Ls kt _ hm).1 (Ne.symm hne)

/-- `rl` on a receipt row: only on the last row. -/
theorem rl_row {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt)
    (j : Nat) (hj : j < total h Lp Lv Ls kt) :
    tr.cell T_RCPT (s + j) rl = if j + 1 = total h Lp Lv Ls kt then 1 else 0 := by
  have hfin := lay.fin
  obtain ⟨f, hf, h1, h2⟩ := plan_cover h Lp Lv Ls kt j hj
  have F := lay.flds f hf
  have hst := F.fld.st (j - f.2.1) (by omega)
  rw [show s + f.2.1 + (j - f.2.1) = s + j by omega] at hst
  have hfe := F.fld.fe (j - f.2.1) (by omega)
  rw [show s + f.2.1 + (j - f.2.1) = s + j by omega] at hfe
  have hhr := F.consts (j - f.2.1) (by omega) Rcpt.hr hrC
  rw [show s + f.2.1 + (j - f.2.1) = s + j by omega, lay.hr] at hhr
  rw [rl_at hL (by omega) (plan_states h Lp Lv Ls kt f hf).1 hst, hfe, hhr]
  have hl := plan_last h Lp Lv Ls kt f hf
  have hle := plan_le h Lp Lv Ls kt f hf
  have key : ((if f.1 = sXRZ then (1 : Fp) else 0) + (if f.1 = sXLH then 1 else 0) *
      (1 - if h = true then 1 else 0)) = if f.2.1 + f.2.2 = total h Lp Lv Ls kt then 1 else 0 := by
    by_cases e1 : f.1 = sXRZ
    · have := hl.mp (Or.inl e1)
      rw [if_pos e1, if_neg (by rw [e1]; decide), if_pos this]; grind
    · by_cases e2 : f.1 = sXLH
      · cases h
        · have := hl.mp (Or.inr ⟨e2, rfl⟩)
          rw [if_neg e1, if_pos e2, if_pos this]; grind
        · have : ¬ f.2.1 + f.2.2 = total true Lp Lv Ls kt := fun e => by
            rcases hl.mpr e with e' | ⟨_, e'⟩
            · rw [e2] at e'; exact absurd e' (by decide)
            · exact absurd e' (by decide)
          rw [if_neg e1, if_pos e2, if_neg this]; grind
      · have : ¬ f.2.1 + f.2.2 = total h Lp Lv Ls kt := fun e => by
          rcases hl.mpr e with e' | ⟨e', _⟩
          · exact e1 e'
          · exact e2 e'
        rw [if_neg e1, if_neg e2, if_neg this]; grind
  rw [key]
  by_cases e : j - f.2.1 + 1 = f.2.2
  · by_cases e' : f.2.1 + f.2.2 = total h Lp Lv Ls kt
    · rw [if_pos e, if_pos e', if_pos (show j + 1 = total h Lp Lv Ls kt by omega)]; grind
    · rw [if_pos e, if_neg e', if_neg (show ¬ j + 1 = total h Lp Lv Ls kt by omega)]; grind
  · rw [if_neg e, if_neg (show ¬ j + 1 = total h Lp Lv Ls kt by omega)]; grind

end ZkFormal.Near.RcptProof
