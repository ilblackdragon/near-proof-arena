import ZkFormal.Near.Render.Proof.RcptCol

/-!
# ZkFormal.Near.Render.Proof.RcptStr — account-id strings of the honest receipts

`StrOk l`: the character facts the `rcpt` table checks on an account id
(`AccountId.valid`: length `2..64`, characters `[a-z0-9-_.]`, no leading,
trailing or doubled separator), for the receipt data `Df c e r` of a `Good`
batch (`str_ok`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

/-- A separator `- _ .`. -/
def sepB (ch : Nat) : Bool := ch == 45 || ch == 95 || ch == 46

structure StrOk (l : List Nat) : Prop where
  len : 2 ≤ l.length ∧ l.length ≤ 64
  byte : ∀ j, j < l.length → l.getD j 0 < 256
  ch : ∀ j, j < l.length → vch (l.getD j 0) = true
  sep : ∀ j, j < l.length → sepB (l.getD j 0) = true → j ≠ 0 ∧ j + 1 < l.length ∧ sepB (l.getD (j + 1) 0) = false

theorem alnum_vch (c : UInt8) (h : AccountId.isAlnum c = true) : vch c.toNat = true ∧ sepB c.toNat = false := by
  simp only [AccountId.isAlnum, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [vch, sepB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne]
  omega

theorem sep_vch (c : UInt8) (h : AccountId.isSep c = true) : vch c.toNat = true ∧ sepB c.toNat = true := by
  simp only [AccountId.isSep, Bool.or_eq_true, beq_iff_eq] at h
  simp only [vch, sepB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

theorem chars_spec : ∀ (s : Bytes) (b : Bool), AccountId.charsOk b s = true →
    ∀ j, j < s.length → vch ((toNats s).getD j 0) = true ∧
      (sepB ((toNats s).getD j 0) = true → (j = 0 → b = false) ∧ j + 1 < s.length ∧
        sepB ((toNats s).getD (j + 1) 0) = false)
  | [], _, _, j, hj => absurd hj (by simp)
  | c :: cs, b, h, j, hj => by
    simp only [AccountId.charsOk] at h
    by_cases ha : AccountId.isAlnum c = true
    · rw [if_pos ha] at h
      have ih := chars_spec cs false h
      cases j with
      | zero =>
        have := alnum_vch c ha
        simp only [toNats, List.map_cons, List.getD_cons_zero] at *
        refine ⟨this.1, fun hs => ?_⟩
        rw [this.2] at hs; cases hs
      | succ j =>
        have := ih j (by simpa using hj)
        simp only [toNats, List.map_cons, List.getD_cons_succ, List.length_cons] at *
        refine ⟨this.1, fun hs => ⟨fun h0 => by simp at h0, by have := (this.2 hs).2.1; omega, (this.2 hs).2.2⟩⟩
    · rw [if_neg ha] at h
      by_cases hsp : AccountId.isSep c = true
      · rw [if_pos hsp, Bool.and_eq_true, Bool.not_eq_true'] at h
        have ih := chars_spec cs true h.2
        have hv := sep_vch c hsp
        cases j with
        | zero =>
          simp only [toNats, List.map_cons, List.getD_cons_zero, List.getD_cons_succ, List.length_cons] at *
          refine ⟨hv.1, fun _ => ⟨fun _ => h.1, ?_, ?_⟩⟩
          · cases cs with
            | nil => simp [AccountId.charsOk] at h
            | cons _ _ => simp
          · cases cs with
            | nil => simp [AccountId.charsOk] at h
            | cons c' cs' =>
              have := (ih 0 (by simp)).2
              simp only [toNats, List.map_cons, List.getD_cons_zero] at this
              cases hs' : sepB c'.toNat
              · simpa using hs'
              · exact absurd ((this hs').1 trivial) (by simp)
        | succ j =>
          have := ih j (by simpa using hj)
          simp only [toNats, List.map_cons, List.getD_cons_succ, List.length_cons] at *
          refine ⟨this.1, fun hs => ⟨fun h0 => by simp at h0, by have := (this.2 hs).2.1; omega, (this.2 hs).2.2⟩⟩
      · rw [if_neg hsp] at h; cases h

theorem strOk_of (s : Bytes) (h : AccountId.valid s = true) : StrOk (toNats s) := by
  simp only [AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have sp := chars_spec s true h3
  have hl : (toNats s).length = s.length := by simp [toNats]
  refine ⟨by omega, fun j hj => ?_, fun j hj => (sp j (by omega)).1, fun j hj hs => ?_⟩
  · simp only [toNats, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [hl] at hj
    rw [List.getElem?_eq_getElem hj]
    simpa using UInt8.toNat_lt _
  · obtain ⟨a, b, d⟩ := (sp j (by omega)).2 hs
    exact ⟨fun h0 => absurd (a h0) (by simp), by omega, d⟩

section
variable {c : Claim} {e : Ext} (hg : Good c e) {r : Nat} (hr : r < NN e)
include hg hr

theorem rc_mem : e.rc r ∈ e.rs := by
  simp only [Ext.rc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show r < e.rs.length from hr),
    Option.getD_some]
  exact List.getElem_mem _

theorem rc_slice : (e.rc r).inSlice = true := List.all_eq_true.1 hg.inSlice _ (rc_mem hg hr)

theorem pred_ok : StrOk (Df c e r).pred := by
  have := rc_slice hg hr
  simp only [Receipt.inSlice, Receipt.wf, Bool.and_eq_true] at this
  rw [Df_eq hr]; exact strOk_of _ this.1.1.1.1.1.1.1.1

theorem recv_ok : StrOk (Df c e r).recv := by
  have := rc_slice hg hr
  simp only [Receipt.inSlice, Receipt.wf, Bool.and_eq_true] at this
  rw [Df_eq hr]; exact strOk_of _ this.1.1.1.1.1.1.1.2

theorem signer_ok : StrOk (Df c e r).signer := by
  have := rc_slice hg hr
  simp only [Receipt.inSlice, Receipt.wf, Bool.and_eq_true] at this
  rw [Df_eq hr]; exact strOk_of _ this.1.1.1.1.1.1.2

end

end RcptP

end ZkFormal.Near.Render
