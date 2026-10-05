import ZkFormal.Near.Render.Proof.RcptChars3

/-!
# ZkFormal.Near.Render.Proof.RcptEmit — the emission slots (`cEmit`) on the honest rows

The emission cells are the table's own `emits` expressions evaluated on the
row (`fullCell`); `evR_evalF`: an expression reading only current cells, no
selector, evaluates to `evalF` of the cells.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

/-- No next-row column, no selector, no emission column. -/
def emOk (e : Expr) : Bool :=
  colsN e == [] && noPS' e && (colsC e).all (fun x => !(31 ≤ x && x < 43))
where
  noPS' : Expr → Bool
    | .isFirst | .isLast | .isTransition => false
    | .add a d | .mul a d => noPS' a && noPS' d
    | .neg a => noPS' a
    | _ => true

theorem ofNat_neg (a : Nat) : Fp.ofNat ((Render.P - a % Render.P) % Render.P) = -Fp.ofNat a := by
  apply Fp.ext
  rw [Fp.toNat_ofNat, Fp.neg_def, Fp.toNat_neg, Fp.toNat_ofNat]
  simp [P_def, Nat.mod_mod]

theorem evR_evalF {cur nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} {f : Nat → Nat} {pubA : Array Nat}
    (hpub : ∀ i, pub.getD i 0 = Fp.ofNat (pubA.getD i 0)) :
    ∀ e, colsN e = [] → emOk.noPS' e = true → (∀ x ∈ colsC e, cur x = Fp.ofNat (f x)) →
      evR cur nx fst lst pub e = Fp.ofNat (evalF f pubA e)
  | .const v, _, _, _ => by simp only [evR_const, evalF, ofNat_mod]; rfl
  | .col x false, _, _, h => by simp only [evalF, ofNat_mod]; exact h x (by simp [colsC])
  | .col x true, h, _, _ => by simp [colsN] at h
  | .pub i, _, _, _ => by simp only [evR_pub, evalF, ofNat_mod, hpub]
  | .isFirst, _, h, _ => by simp [emOk.noPS'] at h
  | .isLast, _, h, _ => by simp [emOk.noPS'] at h
  | .isTransition, _, h, _ => by simp [emOk.noPS'] at h
  | .add a d, h1, h2, h3 => by
    simp only [colsN, List.append_eq_nil_iff, Bool.and_eq_true, emOk.noPS'] at h1 h2
    simp only [evR_add, evalF, ofNat_mod]
    rw [evR_evalF hpub a h1.1 h2.1 (fun x hx => h3 x (by simp [colsC, hx])),
      evR_evalF hpub d h1.2 h2.2 (fun x hx => h3 x (by simp [colsC, hx])), ofNat_add']
  | .mul a d, h1, h2, h3 => by
    simp only [colsN, List.append_eq_nil_iff, Bool.and_eq_true, emOk.noPS'] at h1 h2
    simp only [evR_mul, evalF, ofNat_mod]
    rw [evR_evalF hpub a h1.1 h2.1 (fun x hx => h3 x (by simp [colsC, hx])),
      evR_evalF hpub d h1.2 h2.2 (fun x hx => h3 x (by simp [colsC, hx])), ofNat_mul']
  | .neg a, h1, h2, h3 => by
    simp only [colsN, emOk.noPS'] at h1 h2
    simp only [evR_neg, evalF]
    rw [evR_evalF hpub a h1 h2 (fun x hx => h3 x (by simp [colsC, hx])), ofNat_neg]

theorem emits_ok : Rcpt.emits.all (fun se => (4 ≤ se.1 && se.1 ≤ 26) && decide (emitsOf se.1 = se.2) &&
    se.2.all (fun em => (List.range 4).all (fun k => emOk (emSel em k)))) = true := by decide

theorem eSlots : ∀ e, e < 3 → Rcpt.eId e = 31 + 4 * e ∧ Rcpt.ePos e = 32 + 4 * e ∧ Rcpt.eV e = 33 + 4 * e ∧
    Rcpt.eG e = 34 + 4 * e := by decide

theorem pub_eq (c : WfClaim) (e : Ext) (i : Nat) : (publicOf c).getD i 0 = Fp.ofNat ((PA c.1 e).getD i 0) := by
  simp only [publicOf, PA, pubArr, mkInfo_c, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD, List.getElem?_map, toNats]
  cases c.1.encode[i]? <;> rfl

theorem seg_state_one {c : Claim} {e : Ext} {r s i : Nat} (h1 : 5 ≤ s) (h2 : s ≤ 26) :
    Cc c e (.seg r s i) s = 1 := by
  rw [Cc_seg _ _ _ _ _ _ (by omega)]
  simp only [segCell, show s < 31 by omega, if_true, show s ≠ 0 by omega, show s ≠ 1 by omega,
    show s ≠ 2 by omega, show s ≠ 3 by omega, show s ≠ 27 by omega, show s ≠ 28 by omega,
    show s ≠ 29 by omega, show s ≠ 30 by omega, show s ≠ 4 by omega, if_false]

theorem fields_range {h : Bool} {s : Nat} (hs : s ∈ fields h) : 5 ≤ s ∧ s ≤ 26 := by
  cases h <;> simp [fields] at hs <;> omega

/-- A record row in range: its state cell is `1`, the other state cells `0`. -/
theorem state_cells {c : Claim} {e : Ext} {ρ : RRec} (hρ : RecOk (NN e) (Df c e) ρ) :
    Cc c e ρ (stateOf ρ) = 1 ∧ (∀ s, 4 ≤ s → s ≤ 26 → s ≠ stateOf ρ → Cc c e ρ s = 0) ∧ 4 ≤ stateOf ρ ∧
      stateOf ρ ≤ 26 := by
  cases ρ with
  | cl i =>
    refine ⟨L_sCL c e i, fun s h1 h2 hne => ?_, Nat.le_refl _, by simp [stateOf, Rcpt.sCL]⟩
    simp only [stateOf, Rcpt.sCL] at hne
    have : s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨
        s = 16 ∨ s = 17 ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 ∨ s = 26 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Cc_cl, clCell, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceEqDiff, ↓reduceIte,
      ite_self, and_false, false_and, and_true, true_and]
  | seg r s i =>
    obtain ⟨-, hs, -⟩ := hρ
    have := fields_range hs
    refine ⟨seg_state_one this.1 this.2, fun s' h1 h2 hne => ?_, by simp [stateOf]; omega, by simp [stateOf]; omega⟩
    simp only [stateOf] at hne
    by_cases h4 : s' = 4
    · subst h4; exact S_sCL c e r s i
    · exact Cc_state0 (by omega) h2 hne

theorem Cc_em {c : Claim} {e : Ext} (ρ : RRec) {k j : Nat} (hk : k < 3) (hj : j < 4) :
    Cc c e ρ (31 + 4 * k + j) = match (emitsOf (stateOf ρ))[k]? with
      | some em => evalF (baseCell (DS c e) (PA c e) (BG c) (NN e) ρ) (PA c e) (emSel em j)
      | none => 0 := by
  rw [Cc, fullCell, if_pos (by omega)]
  simp only [show (31 + 4 * k + j - 31) / 4 = k by omega, show (31 + 4 * k + j - 31) % 4 = j by omega]
  cases (emitsOf (stateOf ρ))[k]? <;> rfl

theorem base_eq {c : Claim} {e : Ext} (ρ : RRec) {x : Nat} (hx : ¬ (31 ≤ x ∧ x < 43)) :
    baseCell (DS c e) (PA c e) (BG c) (NN e) ρ x = Cc c e ρ x := by
  simp only [Cc, fullCell, hx, if_false]

theorem gates_ok : Rcpt.emits.all (fun se => se.2.all (fun em =>
    decide (emSel em 3 = Dsl.k 1) || decide (emSel em 3 = Dsl.c 55) || decide (emSel em 3 = Dsl.c 137))) = true := by
  decide

theorem cell_bit {c : Claim} {e : Ext} (ρ : RRec) (x : Nat) (hx : x = 55 ∨ x = 137) : Cc c e ρ x ≤ 1 := by
  rcases hx with rfl | rfl <;> cases ρ
  · rw [show (55 : Nat) = Rcpt.hr from rfl, L_hr]; omega
  · rw [show (55 : Nat) = Rcpt.hr from rfl, S_hr]; unfold b2n; split <;> omega
  · rw [show (137 : Nat) = Rcpt.lo4 from rfl, L_lo4]; unfold b2n; split <;> omega
  · rw [show (137 : Nat) = Rcpt.lo4 from rfl, S_lo4]; omega

/-- **`cEmit` on a record row.** -/
theorem emit_rec {c : WfClaim} {e : Ext} {ρ : RRec} (hρ : RecOk (NN e) (Df c.1 e) ρ) {nx : Nat → Fp}
    {fst lst : Bool} : ∀ x ∈ Rcpt.cEmit, evR (cF c.1 e ρ) nx fst lst (publicOf c) x = 0 := by
  obtain ⟨hst1, hst0, hlo, hhi⟩ := state_cells hρ
  have hcur : ∀ y, ¬ (31 ≤ y ∧ y < 43) → cF c.1 e ρ y = Fp.ofNat (baseCell (DS c.1 e) (PA c.1 e) (BG c.1) (NN e) ρ y) :=
    fun y hy => by rw [base_eq ρ hy]; rfl
  have hev : ∀ em ∈ emitsOf (stateOf ρ), ∀ j, j < 4 →
      evR (cF c.1 e ρ) nx fst lst (publicOf c) (emSel em j) =
        Fp.ofNat (evalF (baseCell (DS c.1 e) (PA c.1 e) (BG c.1) (NN e) ρ) (PA c.1 e) (emSel em j)) := by
    intro em hem j hj
    have hall := List.all_eq_true.1 emits_ok
    -- the state's entry
    have hmem : (stateOf ρ, emitsOf (stateOf ρ)) ∈ Rcpt.emits ∨ emitsOf (stateOf ρ) = [] := by
      unfold emitsOf
      cases hf : Rcpt.emits.find? (fun x => x.1 == stateOf ρ) with
      | none => right; rfl
      | some se =>
        left
        have h1 := List.mem_of_find?_eq_some hf
        have h2 := List.find?_some hf
        simp only [beq_iff_eq] at h2
        rw [← h2]; simpa using h1
    rcases hmem with hmem | hmem
    · have := hall _ hmem
      simp only [Bool.and_eq_true, List.all_eq_true] at this
      have hok := this.2 em hem j (List.mem_range.2 hj)
      simp only [emOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
      obtain ⟨⟨h1, h2⟩, h3⟩ := hok
      exact evR_evalF (pub_eq c e) _ h1 h2 (fun y hy => hcur y (by
        have := h3 y hy; simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
        omega))
    · rw [hmem] at hem; cases hem
  have hact : cF c.1 e ρ Rcpt.act = 1 := by
    cases ρ with
    | cl i => simp only [cF, L_act]; rfl
    | seg r s i => simp only [cF, S_act]; rfl
  intro x hx
  simp only [Rcpt.cEmit, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap] at hx
  rcases hx with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | ⟨⟨s, ems⟩, hse, k, hk, hx⟩
  · obtain ⟨-, -, -, hG⟩ := eSlots k hk
    simp only [evR_bool, evR_c, hG]
    have hv : cF c.1 e ρ (34 + 4 * k) = Fp.ofNat (Cc c.1 e ρ (31 + 4 * k + 3)) := by
      rw [show 34 + 4 * k = 31 + 4 * k + 3 by omega]; rfl
    rw [hv, Cc_em ρ hk (by decide)]
    cases hm : (emitsOf (stateOf ρ))[k]? with
    | none => simp only [ofNat0]; grind
    | some em =>
      simp only
      have hmem : em ∈ emitsOf (stateOf ρ) := List.mem_of_getElem? hm
      have hg : emSel em 3 = Dsl.k 1 ∨ emSel em 3 = Dsl.c 55 ∨ emSel em 3 = Dsl.c 137 := by
        have hall := List.all_eq_true.1 gates_ok
        unfold emitsOf at hmem
        cases hf : Rcpt.emits.find? (fun x => x.1 == stateOf ρ) with
        | none => rw [hf] at hmem; cases hmem
        | some se =>
          rw [hf] at hmem
          have := List.all_eq_true.1 (hall se (List.mem_of_find?_eq_some hf)) em hmem
          simpa [Bool.or_eq_true, decide_eq_true_eq, or_assoc] using this
      rcases hg with hg | hg | hg <;> rw [hg]
      · simp only [Dsl.k, evalF, ofNat_mod, ofNat1]; grind
      · simp only [Dsl.c, evalF, ofNat_mod]
        rw [base_eq ρ (by decide)]
        have := cell_bit (c := c.1) (e := e) ρ 55 (Or.inl rfl)
        rcases (show Cc c.1 e ρ 55 = 0 ∨ Cc c.1 e ρ 55 = 1 by omega) with h | h <;> rw [h] <;>
          simp only [ofNat0, ofNat1] <;> grind
      · simp only [Dsl.c, evalF, ofNat_mod]
        rw [base_eq ρ (by decide)]
        have := cell_bit (c := c.1) (e := e) ρ 137 (Or.inr rfl)
        rcases (show Cc c.1 e ρ 137 = 0 ∨ Cc c.1 e ρ 137 = 1 by omega) with h | h <;> rw [h] <;>
          simp only [ofNat0, ofNat1] <;> grind
  · simp only [evR_mul, evR_not, evR_c, hact]; grind
  · have hok := List.all_eq_true.1 emits_ok _ hse
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨h4, h26⟩, hems⟩, -⟩ := hok
    simp only at hx h4 h26 hems
    by_cases hs : s = stateOf ρ
    · subst hs
      rw [← hems] at hx
      obtain ⟨hI, hP, hV, hG⟩ := eSlots k hk
      have hcell : ∀ j, j < 4 → cF c.1 e ρ (31 + 4 * k + j) = Fp.ofNat (match (emitsOf (stateOf ρ))[k]? with
          | some em => evalF (baseCell (DS c.1 e) (PA c.1 e) (BG c.1) (NN e) ρ) (PA c.1 e) (emSel em j)
          | none => 0) := fun j hj => by simp only [cF, Cc_em ρ hk hj]
      cases hm : (emitsOf (stateOf ρ))[k]? with
      | none =>
        rw [hm] at hx
        simp only [List.mem_singleton] at hx
        subst hx
        have := hcell 3 (by decide)
        rw [hm] at this
        simp only [evR_mul, evR_c, hG, show 34 + 4 * k = 31 + 4 * k + 3 by omega, this, ofNat0]; grind
      | some em =>
        rw [hm] at hx
        obtain ⟨id, p, v, g⟩ := em
        have hmem : (id, p, v, g) ∈ emitsOf (stateOf ρ) := List.mem_of_getElem? hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        have hs1 : cF c.1 e ρ (stateOf ρ) = 1 := by simp only [cF, hst1]; rfl
        have hj : ∀ j, j < 4 → cF c.1 e ρ (31 + 4 * k + j) =
            evR (cF c.1 e ρ) nx fst lst (publicOf c) (emSel (id, p, v, g) j) := by
          intro j hj; rw [hcell j hj, hm, hev _ hmem j hj]
        have e0 := hj 0 (by decide)
        have e1 := hj 1 (by decide)
        have e2 := hj 2 (by decide)
        have e3 := hj 3 (by decide)
        rw [Nat.add_zero] at e0
        rw [show 31 + 4 * k + 1 = 32 + 4 * k by omega] at e1
        rw [show 31 + 4 * k + 2 = 33 + 4 * k by omega] at e2
        rw [show 31 + 4 * k + 3 = 34 + 4 * k by omega] at e3
        simp only [emSel] at e0 e1 e2 e3
        rcases hx with rfl | rfl | rfl | rfl <;>
          simp only [evR_mul, evR_sub, evR_c, hs1, hI, hP, hV, hG, e0, e1, e2, e3] <;> grind
    · have h0 : cF c.1 e ρ s = 0 := by simp only [cF, hst0 s h4 h26 hs]; rfl
      cases hm : ems[k]? with
      | none => rw [hm] at hx; simp only [List.mem_singleton] at hx; subst hx; simp only [evR_mul, evR_c, h0]; grind
      | some em =>
        rw [hm] at hx
        obtain ⟨id, p, v, g⟩ := em
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp only [evR_mul, evR_c, h0] <;> grind

theorem emit_zrP : Rcpt.cEmit.all (Zr (fun _ => true) (fun _ => false) true) = true := by decide

theorem lastRec_mem {c : Claim} {e : Ext} (hg : Good c e) : lastRec c e ∈ RL c e :=
  List.mem_of_getLast? (RL_last hg)

/-- **`cEmit` on the honest rows.** -/
theorem emit_ok {c : WfClaim} {e : Ext} (hg : Good c.1 e) :
    ∀ x ∈ Rcpt.cEmit, ∀ q, q < (render c.1 e).height T_RCPT → x.eval (render c.1 e) T_RCPT q (publicOf c) = 0 := by
  intro x hx
  apply allRows_of hg
  · intro ρ hρ _ _; exact emit_rec (RL_ok hg ρ hρ) x hx
  · exact emit_rec (RL_ok hg _ (lastRec_mem hg)) x hx
  · exact zr_pad (zn := fun _ => false) (fun _ h => by cases h) (List.all_eq_true.1 emit_zrP x hx)
  · exact zr_pad (zn := fun _ => false) (fun _ h => by cases h) (List.all_eq_true.1 emit_zrP x hx)

end RcptP

end ZkFormal.Near.Render
