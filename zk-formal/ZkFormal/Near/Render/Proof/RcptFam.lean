import ZkFormal.Near.Render.Proof.RcptLocal

/-!
# ZkFormal.Near.Render.Proof.RcptFam — a constraint family on every row, by row kind

`fam_of`: a list of constraints holds on every row of the honest `rcpt` table
once it holds on the claim rows, inside a field, at a field's end (same
receipt), at a receipt's end (next receipt), on the last record, and on the
padding rows.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

theorem fam_of {c : Claim} {e : Ext} (hg : Good c e) {pub : List Fp} {F : List Expr}
    (hcl : ∀ i, i < 12 → ∀ x ∈ F,
      evR (cF c e (.cl i)) (cF c e (nextOf (Df c e) (.cl i))) (decide (i = 0)) false pub x = 0)
    (hin : ∀ r s i, r < NN e → s ∈ fields (Df c e r).hr → i + 1 < fLen (Df c e r) s → ∀ x ∈ F,
      evR (cF c e (.seg r s i)) (cF c e (.seg r s (i + 1))) false false pub x = 0)
    (hfe : ∀ r s i, r < NN e → s ∈ fields (Df c e r).hr → i + 1 = fLen (Df c e r) s →
      isRl (Df c e r) s i = false → ∀ x ∈ F,
      evR (cF c e (.seg r s i)) (cF c e (.seg r (nextF (Df c e r).hr s) 0)) false false pub x = 0)
    (hrl : ∀ r s i, r + 1 < NN e → s ∈ fields (Df c e r).hr → i + 1 = fLen (Df c e r) s →
      isRl (Df c e r) s i = true → ∀ x ∈ F,
      evR (cF c e (.seg r s i)) (cF c e (.seg (r + 1) 5 0)) false false pub x = 0)
    (hlast : ∀ x ∈ F, evR (cF c e (lastRec c e)) (fun _ => 0) false false pub x = 0)
    (hP : ∀ x ∈ F, evR (fun _ => 0) (fun _ => 0) false false pub x = 0)
    (hW : ∀ x ∈ F, evR (fun _ => 0) (cF c e (.cl 0)) false true pub x = 0) :
    ∀ x ∈ F, ∀ q, q < (render c e).height T_RCPT → x.eval (render c e) T_RCPT q pub = 0 := by
  intro x hx
  apply allRows_of hg
  · intro ρ hρ _ hnx
    have hok := RL_ok hg ρ hρ
    cases ρ with
    | cl i =>
      have hb : (RRec.cl i == RRec.cl 0) = decide (i = 0) := by by_cases h : i = 0 <;> simp [h]
      rw [hb]; exact hcl i hok x hx
    | seg r s i =>
      rw [seg_ne_cl]
      obtain ⟨hr, hs, hi⟩ := hok
      by_cases h1 : i + 1 < fLen (Df c e r) s
      · rw [nextOf_in h1]; exact hin r s i hr hs h1 x hx
      · have hfe' : i + 1 = fLen (Df c e r) s := by omega
        cases hrl' : isRl (Df c e r) s i
        · have hn : nextOf (Df c e) (.seg r s i) = .seg r (nextF (Df c e r).hr s) 0 := by
            simp [nextOf, h1, hrl']
          rw [hn]; exact hfe r s i hr hs hfe' hrl' x hx
        · have hn : nextOf (Df c e) (.seg r s i) = .seg (r + 1) 5 0 := by simp [nextOf, h1, hrl']
          rw [hn] at hnx ⊢
          exact hrl r s i (RL_ok hg _ hnx).1 hs hfe' hrl' x hx
  · exact hlast x hx
  · exact hP x hx
  · exact hW x hx

theorem Zr_mono {z z' zn zn' : Nat → Bool} {f0 f0' : Bool} (hz : ∀ x, z x = true → z' x = true)
    (hzn : ∀ x, zn x = true → zn' x = true) (hf : f0 = true → f0' = true) :
    ∀ {e}, Zr z zn f0 e = true → Zr z' zn' f0' e = true
  | .const _, h' => h'
  | .col x false, h' => hz x h'
  | .col x true, h' => hzn x h'
  | .pub _, h' => h'
  | .isFirst, h' => hf h'
  | .isLast, h' => h'
  | .isTransition, h' => h'
  | .add a d, h' => by
    simp only [Zr, Bool.and_eq_true] at h' ⊢; exact ⟨Zr_mono hz hzn hf h'.1, Zr_mono hz hzn hf h'.2⟩
  | .mul a d, h' => by
    simp only [Zr, Bool.or_eq_true] at h' ⊢
    rcases h' with h' | h'
    · exact .inl (Zr_mono hz hzn hf h')
    · exact .inr (Zr_mono hz hzn hf h')
  | .neg a, h' => by simp only [Zr] at h' ⊢; exact Zr_mono hz hzn hf h'

/-- The last record. -/
theorem lastRec_facts {c : Claim} {e : Ext} (hg : Good c e) :
    ∃ r s i, lastRec c e = .seg r s i ∧ r + 1 = NN e ∧ s ∈ fields (Df c e r).hr ∧ i + 1 = fLen (Df c e r) s ∧
      isRl (Df c e r) s i = true ∧ (s = 23 ∨ s = 26) := by
  have hN := NN_pos hg
  have hd := D_ok hg (NN e - 1) (by omega)
  have hs : lastF (Df c e (NN e - 1)).hr ∈ fields (Df c e (NN e - 1)).hr := by
    cases (Df c e (NN e - 1)).hr <;> simp [fields, lastF]
  have hp := fLen_pos hd.2 hs
  refine ⟨_, _, _, rfl, by omega, hs, by omega, lastF_rl hd.2, ?_⟩
  unfold lastF; split <;> simp

end RcptP

end ZkFormal.Near.Render
