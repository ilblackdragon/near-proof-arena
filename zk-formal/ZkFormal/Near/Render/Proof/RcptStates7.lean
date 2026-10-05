import ZkFormal.Near.Render.Proof.RcptStates6

/-!
# ZkFormal.Near.Render.Proof.RcptStates7 — `cStates` on the honest rows (`states_ok`)
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

theorem states_zrP : Rcpt.cStates.all (Zr (fun _ => true) (fun _ => true) true) = true := by decide

theorem states_zrW : Rcpt.cStates.all (fun x => decide (x = mul3 .isTransition (Dsl.not (Dsl.c Rcpt.act))
    (Dsl.n Rcpt.act)) || Zr (fun _ => true) (fun _ => false) true x) = true := by decide

/-- **`cStates` on the honest rows.** -/
theorem states_ok {c : Claim} {e : Ext} (hg : Good c e) {pub : List Fp} :
    ∀ x ∈ Rcpt.cStates, ∀ q, q < (render c e).height T_RCPT → x.eval (render c e) T_RCPT q pub = 0 := by
  intro x hx
  have hkt : ∀ ρ ∈ RL c e, ∀ r s i, ρ = .seg r s i → (Df c e r).kt ≤ 1 := by
    intro ρ hρ r s i h; subst h; exact d_kt hg (RL_ok hg _ hρ).1
  rw [cStates_eq] at hx
  have hx' : x ∈ sA ∨ x ∈ sB ++ sC ++ sD ++ sE ++ sF ++ sG ++ sH := by
    simp only [List.mem_append] at hx ⊢
    rcases hx with ((((((h | h) | h) | h) | h) | h) | h) | h
    · exact .inl h
    all_goals right; simp [h]
  apply allRows_of hg
  · intro ρ hρ hne hnx
    have hok := RL_ok hg ρ hρ
    rcases hx' with hA | hx'
    · exact sA_rec hok (hkt ρ hρ) x hA
    cases ρ with
    | cl i =>
      have := cl_rows hg (pub := pub) (show i < 12 from hok) x hx'
      have hb : (RRec.cl i == RRec.cl 0) = decide (i = 0) := by
        by_cases h : i = 0 <;> simp [h]
      rw [hb]; exact this
    | seg r s i =>
      rw [seg_ne_cl]
      obtain ⟨hr, hs, hi⟩ := hok
      by_cases h1 : i + 1 < fLen (Df c e r) s
      · rw [nextOf_in h1]; exact seg_inner (RL_ok hg _ hρ) h1 (d_ge hg hr) x hx'
      · have hfe : i + 1 = fLen (Df c e r) s := by omega
        cases hrl : isRl (Df c e r) s i
        · have hn : nextOf (Df c e) (.seg r s i) = .seg r (nextF (Df c e r).hr s) 0 := by
            simp [nextOf, h1, hrl]
          rw [hn]; exact seg_fe (RL_ok hg _ hρ) hfe hrl (d_ge hg hr) x hx'
        · have hn : nextOf (Df c e) (.seg r s i) = .seg (r + 1) 5 0 := by simp [nextOf, h1, hrl]
          rw [hn] at hnx ⊢
          have := (RL_ok hg _ hnx).1
          exact seg_rl hg (RL_ok hg _ hρ) hfe hrl this x hx'
  · have hN := NN_pos hg
    have hm := lastRec_mem hg
    have hok := RL_ok hg _ hm
    rcases hx' with hA | hx'
    · exact sA_rec hok (hkt _ hm) x hA
    simp only [lastRec] at hok ⊢
    have hd := D_ok hg (NN e - 1) (by omega)
    have hp := fLen_pos hd.2 (show lastF (Df c e (NN e - 1)).hr ∈ fields (Df c e (NN e - 1)).hr by
      cases (Df c e (NN e - 1)).hr <;> simp [fields, lastF])
    exact seg_last hok (by omega) (lastF_rl hd.2) (by omega) hd.1 (d_ge hg (by omega)) x hx'
  · exact zr_pad (zn := fun _ => true) (fun _ _ => rfl) (List.all_eq_true.1 states_zrP x hx)
  · have h := List.all_eq_true.1 states_zrW x hx
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | h
    · simp only [evR_mul3, evR_isTransition, ↓reduceIte]; grind
    · exact zr_pad (zn := fun _ => false) (fun _ h => by cases h) h

end RcptP

end ZkFormal.Near.Render
