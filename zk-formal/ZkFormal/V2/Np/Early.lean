import ZkFormal.V2.Np.Frame

/-!
# ZkFormal.V2.Np.Early — `Msg0`, `Msg2`, `Msg6`, `Chal5`, `Chal7` for v2

Copies of v1's proofs (`Udr.Np.Early`, `Ali`, `Chal7`) in which the bus disjunct is
v2's (`FpDifferP`, `BusFinalsFailP`).  These rounds treat it as a frame.
-/

namespace ZkFormal.V2.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2

theorem msg0P : MsgAtP 0 := by
  intro AP prm _ τ m _ _ _ hE hst
  have hE' : (τ.push m).entries.length = 1 := by rw [len_push, hE]
  simp only [StageP, hE] at hst
  simp only [StageP, hE']
  exact Or.inr fun hH => hst ⟨_, hH⟩

theorem msg2P : MsgAtP 2 := by
  intro AP prm _ τ m _ hs _ hE hst
  have hs' : Shaped (Vnp AP.toAir prm) (τ.push m) := (shaped_iff AP prm _).mp hs
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, _, _, s, h1, h2⟩ := push_fits hs' hne
  rw [hE, (sched_get l).2.1] at h1; cases h1
  have hm : m = [] := by have := fits_nil h2; cases this; rfl
  subst hm
  have hE' : (τ.push []).entries.length = 3 := by rw [len_push, hE]
  have hO := oAgree_push_nil τ hne 1
  simp only [StageP, hE] at hst
  simp only [StageP, hE', chals_push]
  rw [allClose_congr hO (by omega), localFail_congr hO (by omega), fpDifferP_congr AP prm hO (by omega)]
  exact hst

theorem msg6P : MsgAtP 6 := by
  intro AP prm _ τ m _ hs _ hE hst
  have hs' : Shaped (Vnp AP.toAir prm) (τ.push m) := (shaped_iff AP prm _).mp hs
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  have hsτ := (shapedPrefix AP.toAir prm τ).1 m hs'
  obtain ⟨ho2, hel⟩ := shaped_oracles2 hsτ (by omega)
  obtain ⟨l, hl, hok, _⟩ := shaped_hdr hsτ hne
  obtain ⟨hlen, hlog, hwf, _⟩ := headerOk_facts hok
  have hO : OAgree 2 (τ.push m) τ := (oAgree_push τ m hne).mono ho2
  have hF := finalsOf_push τ m hel
  have hE' : (τ.push m).entries.length = 7 := by rw [len_push, hE]
  simp only [StageP, hE] at hst
  simp only [StageP, hE', chals_push]
  rcases hst with h | ⟨t, ht, r, hr, hC⟩ | h
  · exact Or.inl fun h3 => h ((allClose_congr hO (by omega)).mp (allClose_mono (by omega) h3))
  · refine Or.inr (Or.inl ⟨t, ht, omg (tl AP.toAir prm τ t).log ^ r, ?_⟩)
    rw [Ct_congr hO (by omega) hF, tl_congr _ prm (header?_push τ m hne)]
    have hlt : (tl AP.toAir prm τ t).log ≤ 27 := by
      rw [tl_eq hl hlen t ht]
      have := (table_wf_facts ((wf_facts hwf).1 _ (List.getElem_mem ht))).2.1
      have := (hlog t ht (by omega)).2.1
      show l[t] ≤ 27; omega
    rw [omg_pow_r_T hlt]
    intro he; apply hC; rw [he]; grind
  · exact Or.inr (Or.inr ((busFinalsFailP_congr AP prm (header?_push τ m hne) hF rfl _ _).mpr h))

theorem chal5P : ChalAtP 5 := by
  intro AP prm hok τ _ hs _ hE hst
  have hs' : Shaped (Vnp AP.toAir prm) τ := (shaped_iff AP prm _).mp hs
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  have hcl : τ.chals.length = 2 := by rw [shaped_chals_length hs', hE]
  have hlast := chals_getD_pushChal_last τ
  rw [hcl] at hlast
  have h0 : ∀ c, (τ.pushChal c).chals.getD 0 0 = τ.chals.getD 0 0 := fun c =>
    chals_getD_pushChal τ c 0 (by omega)
  have h1 : ∀ c, (τ.pushChal c).chals.getD 1 0 = τ.chals.getD 1 0 := fun c =>
    chals_getD_pushChal τ c 1 (by omega)
  have hE' : ∀ c, (τ.pushChal c).entries.length = 6 := fun c => by rw [len_pushChal, hE]
  simp only [StageP, hE] at hst
  have hstage : ∀ c, StageP AP prm (τ.pushChal c) ↔ (¬ AllClose AP.toAir prm τ 2 ∨
      (∃ t, t < AP.tables.length ∧ ∃ r, r < 2 ^ (tl AP.toAir prm τ t).log ∧
        Ct AP.toAir prm τ t (τ.chals.getD 0 0) (τ.chals.getD 1 0) c (omg (tl AP.toAir prm τ t).log ^ r) ≠ 0) ∨
      BusFinalsFailP AP prm τ (τ.chals.getD 0 0) (τ.chals.getD 1 0)) := fun c => by
    have hO := oAgree_pushChal τ c hne 2
    simp only [StageP, hE' c, h0, h1, hlast]
    rw [allClose_congr hO (by omega),
      busFinalsFailP_congr AP prm (header?_pushChal τ c hne) (finalsOf_pushChal τ c) rfl]
    simp only [tl_congr _ prm (header?_pushChal τ c hne), Ct_congr hO (Nat.le_refl 2) (finalsOf_pushChal τ c)]
  rcases hst with h | ⟨t, ht, r, hr, v, hv, hv0⟩ | h
  · exact Nat.le_trans (count_doom_leP AP prm (fun _ => False)
      fun c _ => (hstage c).mpr (Or.inl h)) (count_false_le _ _)
  · refine Nat.le_trans (count_doom_leP AP prm
      (fun c => combine c (csAt AP.toAir prm τ t (τ.chals.getD 0 0) (τ.chals.getD 1 0)
        (omg (tl AP.toAir prm τ t).log ^ r)) = 0)
      fun c hc => (hstage c).mpr (Or.inr (Or.inl ⟨t, ht, r, hr, hc⟩))) ?_
    have := count_combine_lt hv hv0
    have := csAt_length hok.1 τ t ht (τ.chals.getD 0 0) (τ.chals.getD 1 0) (omg (tl AP.toAir prm τ t).log ^ r)
    unfold badBudget; omega
  · exact Nat.le_trans (count_doom_leP AP prm (fun _ => False)
      fun c _ => (hstage c).mpr (Or.inr (Or.inr h))) (count_false_le _ _)

theorem chal7P : ChalAtP 7 := by
  intro AP prm hok τ _ hs _ hE hst
  obtain ⟨⟨hprm, _, _⟩, _⟩ := hok
  subst hprm
  have hs' : Shaped (Vnp AP.toAir Params.default) τ := (shaped_iff AP _ _).mp hs
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, hl, hh, _⟩ := shaped_hdr hs' hne
  obtain ⟨hlen, hlog, hwf, hdegs⟩ := headerOk_facts hh
  have hcl : τ.chals.length = 3 := by rw [shaped_chals_length hs', hE]
  have hlast := chals_getD_pushChal_last τ
  rw [hcl] at hlast
  have h0 : ∀ c, (τ.pushChal c).chals.getD 0 0 = τ.chals.getD 0 0 := fun c =>
    chals_getD_pushChal τ c 0 (by omega)
  have h1 : ∀ c, (τ.pushChal c).chals.getD 1 0 = τ.chals.getD 1 0 := fun c =>
    chals_getD_pushChal τ c 1 (by omega)
  have h2 : ∀ c, (τ.pushChal c).chals.getD 2 0 = τ.chals.getD 2 0 := fun c =>
    chals_getD_pushChal τ c 2 (by omega)
  have hE' : ∀ c, (τ.pushChal c).entries.length = 8 := fun c => by rw [len_pushChal, hE]
  let prm := Params.default
  let a0 := τ.chals.getD 0 0
  let a1 := τ.chals.getD 1 0
  let a2 := τ.chals.getD 2 0
  have hstage : ∀ c, StageP AP prm (τ.pushChal c) ↔ (¬ c.IsBase ∧ (¬ AllClose AP.toAir prm τ 3 ∨
      (∃ t, t < AP.toAir.tables.length ∧ Ct AP.toAir prm τ t a0 a1 a2 c ≠
        (c ^ (2 ^ (tl AP.toAir prm τ t).log) - 1) * Qt AP.toAir prm τ t c) ∨ BusFinalsFailP AP prm τ a0 a1)) := fun c => by
    have hO := oAgree_pushChal τ c hne 3
    simp only [StageP, hE' c, h0, h1, h2, hlast]
    rw [allClose_congr hO (by omega),
      busFinalsFailP_congr AP prm (header?_pushChal τ c hne) (finalsOf_pushChal τ c) rfl]
    simp only [tl_congr _ prm (header?_pushChal τ c hne), Ct_congr hO (by omega) (finalsOf_pushChal τ c),
      Qt_congr hO (Nat.le_refl 3)]
    exact Iff.rfl
  simp only [StageP, hE] at hst
  have hP : Algebra.P ≤ badBudget := by unfold badBudget; decide
  rcases hst with h | ⟨t, ht, x0, hx0⟩ | h
  · exact Nat.le_trans (count_doom_leP AP prm Fp8.IsBase
      fun c hc => (hstage c).mpr ⟨hc, Or.inl h⟩) (Nat.le_trans count_base_le hP)
  · let T := 2 ^ (tl AP.toAir prm τ t).log
    have hdeg : (tableOf AP.toAir t).degree 1 ≤ 16 := by
      rw [tableOf_lt ht]; exact hdegs _ (List.getElem_mem ht)
    have htl := tl_eq (prm := prm) hl hlen t ht
    have hq : (tl AP.toAir prm τ t).quot ≤ 15 := by
      rw [htl]; show (AP.toAir.tables[t]).degree 1 - 1 ≤ 15
      rw [← tableOf_lt ht]; omega
    have hlogT : (tl AP.toAir prm τ t).log ≤ 22 := by
      rw [htl]
      have := (table_wf_facts ((wf_facts hwf).1 _ (List.getElem_mem ht))).2.1
      have := (hlog t ht (by omega)).2.1
      show l[t] ≤ 22; omega
    have hCt : Dg T 64 (fun x => Ct AP.toAir prm τ t a0 a1 a2 x) := (csAt_rep AP.toAir τ t hdeg a0 a1).combine a2
    have hQt : Dg T 16 (fun x => (x ^ T - 1) * Qt AP.toAir prm τ t x) := by
      have := (Dg.powT.sub (Dg.const 0 1)).mul
        (combine_xT_deg (T := T) (fun q x => colAt AP.toAir prm τ ⟨t, 2, q⟩ x) (fun q => Dg.ev _)
          (List.range (tl AP.toAir prm τ t).quot))
      rw [List.length_range] at this
      exact this.mono (by omega)
    have hφ : Dg T 64 (fun x => Ct AP.toAir prm τ t a0 a1 a2 x - (x ^ T - 1) * Qt AP.toAir prm τ t x) :=
      (hCt.sub hQt).mono (by omega)
    have hcnt := count_roots_of_poly hφ (x0 := x0) (fun h => hx0 (by grind))
    refine Nat.le_trans (count_doom_leP AP prm
      (fun c => c.IsBase ∨ Ct AP.toAir prm τ t a0 a1 a2 c - (c ^ T - 1) * Qt AP.toAir prm τ t c = 0)
      fun c hc => (hstage c).mpr ⟨fun h => hc (Or.inl h), Or.inr (Or.inl ⟨t, ht, fun he => hc
        (Or.inr (by rw [he]; grind))⟩)⟩) ?_
    refine Nat.le_trans (count_or_le _ _ _) ?_
    have hT : T ≤ 2 ^ 22 := Nat.pow_le_pow_right (by decide) hlogT
    have := count_base_le
    unfold badBudget
    have : Algebra.P = 2013265921 := rfl
    omega
  · exact Nat.le_trans (count_doom_leP AP prm Fp8.IsBase
      fun c hc => (hstage c).mpr ⟨hc, Or.inr (Or.inr h)⟩) (Nat.le_trans count_base_le hP)

end ZkFormal.V2.Np
