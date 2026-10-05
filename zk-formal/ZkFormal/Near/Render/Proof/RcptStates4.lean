import ZkFormal.Near.Render.Proof.RcptStates3

/-!
# ZkFormal.Near.Render.Proof.RcptStates4 — boundary constraints (`sG`) at a field's last row
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

macro "sgsimp" : tactic => `(tactic| (try simp only [evR_mul, evR_mul3, evR_sub, evR_add, evR_not, evR_c, evR_n, evR_k,
    evR_smul, evR_sum_cons, evR_sum_nil, evR_isFirst, evR_isLast, evR_isTransition, Rcpt.rowE, Rcpt.varE, cF, rseg,
    Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, b2n_false, b2n_true, Bool.false_eq_true,
    ↓reduceIte, ofNat0, ofNat1, decide_true, decide_false]))

/-- `sG` on a field's last row, not the receipt's last. -/
theorem sG_fe {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s)
    (hrl : isRl (Df c e r) s i = false) (hge : (Df c e r).hr = true → (Df c e r).ge = true) {nx : Nat → Fp}
    {pub : List Fp} (hnx : nx Rcpt.act = 1) :
    ∀ x ∈ sG, evR (cF c e (.seg r s i)) nx false false pub x = 0 := by
  have h2 : s ≠ 26 ∧ (s = 23 → (Df c e r).hr = true) := by
    unfold isRl at hrl
    cases hh : (Df c e r).hr <;> simp [hh, hfe] at hrl ⊢ <;> omega
  have hfe' : decide (i + 1 = fLen (Df c e r) s) = true := by simp [hfe]
  simp only [sG, List.forall_mem_cons, List.forall_mem_nil, and_true]
  and_intros
  all_goals sgsimp
  all_goals (try simp only [hrl, hfe', hnx, b2n_false, b2n_true, ofNat0, ofNat1])
  all_goals first
    | grind
    | (simp only [oEnd_eq, o2End_eq]; grind)
    | (cases h : (Df c e r).hr
       · simp only [b2n_false, ofNat0]; grind
       · simp only [hge h, b2n_true, ofNat1]; grind)
    | (split
       · rename_i h; exact absurd h.symm h2.1
       · split
         · rename_i h h'; have := h2.2 h'.symm; simp only [this, b2n_true, ofNat1]; grind
         · grind)
    | rfin

/-- `sG` on a receipt's last row, followed by the next receipt (`rnx` its cells). -/
theorem sG_rl {c : Claim} {e : Ext} (hg : Good c e) {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s)
    (hrl : isRl (Df c e r) s i = true) (hr : r + 1 < NN e) {pub : List Fp} :
    ∀ x ∈ sG, evR (cF c e (.seg r s i)) (cF c e (.seg (r + 1) 5 0)) false false pub x = 0 := by
  have h2 : s = 26 ∨ (s = 23 ∧ (Df c e r).hr = false) := by
    unfold isRl at hrl
    cases hh : (Df c e r).hr <;> simp [hh] at hrl ⊢ <;> omega
  have hge := d_ge hg (show r < NN e by omega)
  obtain ⟨so, so2, srcnt, -⟩ := d_succ hg hr
  have hr1 := Df_r (c := c) hr
  have hr0 := Df_r (c := c) (show r < NN e by omega)
  have hlast : ((Df c e r).r + 1 == NN e) = false := by simp [hr0]; omega
  have hfe' : decide (i + 1 = fLen (Df c e r) s) = true := by simp [hfe]
  simp only [sG, List.forall_mem_cons, List.forall_mem_nil, and_true]
  and_intros
  all_goals sgsimp
  all_goals (try simp only [hrl, hfe', hlast, hr1, hr0, so, so2, srcnt, Bool.true_and, b2n_false, b2n_true,
    ofNat0, ofNat1])
  all_goals first
    | grind
    | (simp only [oEnd_eq, o2End_eq]; grind)
    | (simp only [ofNat_add_e, ofNat1, natCast_eq]; grind)
    | (cases h : (Df c e r).hr
       · simp only [b2n_false, ofNat0]; grind
       · simp only [hge h, b2n_true, ofNat1]; grind)
    | (rcases h2 with rfl | ⟨rfl, h3⟩ <;> simp only [Nat.reduceEqDiff, ↓reduceIte, ofNat0, ofNat1] <;>
        (try simp only [h3, b2n_false, ofNat0]) <;> grind)
    | rfin

/-- `sG` on the last record row (a padding row next). -/
theorem sG_last {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s)
    (hrl : isRl (Df c e r) s i = true) (hr : r + 1 = NN e) (hr0 : (Df c e r).r = r)
    (hge : (Df c e r).hr = true → (Df c e r).ge = true) {pub : List Fp} :
    ∀ x ∈ sG, evR (cF c e (.seg r s i)) (fun _ => 0) false false pub x = 0 := by
  have h2 : s = 26 ∨ (s = 23 ∧ (Df c e r).hr = false) := by
    unfold isRl at hrl
    cases hh : (Df c e r).hr <;> simp [hh] at hrl ⊢ <;> omega
  have hlast : ((Df c e r).r + 1 == NN e) = true := by simp [hr0, hr]
  have hfe' : decide (i + 1 = fLen (Df c e r) s) = true := by simp [hfe]
  simp only [sG, List.forall_mem_cons, List.forall_mem_nil, and_true]
  and_intros
  all_goals sgsimp
  all_goals (try simp only [hrl, hfe', hlast, Bool.true_and, b2n_false, b2n_true, ofNat0, ofNat1])
  all_goals first
    | grind
    | (simp only [oEnd_eq, o2End_eq]; grind)
    | (cases h : (Df c e r).hr
       · simp only [b2n_false, ofNat0]; grind
       · simp only [hge h, b2n_true, ofNat1]; grind)
    | (rcases h2 with rfl | ⟨rfl, h3⟩ <;> simp only [Nat.reduceEqDiff, ↓reduceIte, ofNat0, ofNat1] <;>
        (try simp only [h3, b2n_false, ofNat0]) <;> grind)
    | rfin

end RcptP

end ZkFormal.Near.Render
