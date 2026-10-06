import ZkFormal.V2.Np.Defs

/-!
# ZkFormal.V2.Np.Compose — `RbrWith` of np-udr-stark-v2 from the obligations

Mirrors `Udr.Np.Compose`.  Shape facts are v1's (`shapedPrefix`, `scheduleAlt` at
`AP.toAir`): the v2 verifier has v1's header check and schedule.  The claim-only
disjunct `PubBad` is preserved by every transition (it depends on `τ.cb` only) and
excluded at the query phase by `global` (v2's `globalOk` contains `pubFit`).
-/

namespace ZkFormal.V2.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2

theorem pubBad_push (AP : AirP) (τ : PTn) (m : List (PartV Fp8 (Oracle Fp))) :
    PubBad AP (τ.push m) ↔ PubBad AP τ := Iff.rfl

theorem pubBad_pushChal (AP : AirP) (τ : PTn) (c : Fp8) :
    PubBad AP (τ.pushChal c) ↔ PubBad AP τ := Iff.rfl

/-- `global` of v2 implies that the public segments fit. -/
theorem pubFit_of_global (AP : AirP) (prm : Params) (τ : PTn)
    (h : (VnpP AP prm).global ((VnpP AP prm).prep τ.erase) = true) : ¬ PubBad AP τ := by
  change (prepP (F := Fp) AP prm τ.erase).globalOk = true at h
  rw [prepP_eq] at h
  change globalOkP (F := Fp) (K := Fp8) AP prm τ.erase = true at h
  unfold globalOkP at h
  intro hb
  unfold PubBad pubT pubOf at hb
  split at h
  · cases h
  · split at h
    · simp only [PT.erase, Bool.and_eq_true] at h
      rw [hb] at h
      exact Bool.false_ne_true h.1.2
    · cases h

theorem rbrWithP_of (hSP : ShapedPrefixStmt) (hAlt : ScheduleAltStmt)
    (h0 : MsgAtP 0) (h2 : MsgAtP 2) (h4 : MsgAtP 4) (h6 : MsgAtP 6) (h8 : MsgAtP 8)
    (hML : ∀ k, 10 ≤ k → MsgAtP k) (c1 : ChalAtP 1) (c3 : ChalAtP 3) (c5 : ChalAtP 5) (c7 : ChalAtP 7)
    (cL : ∀ k, 9 ≤ k → ChalAtP k) (hQ : QueryStmtP) (AP : AirP) (prm : Params) (hok : NpOkP AP prm) :
    RbrWith (VnpP AP prm) (AirLangP AP) Fp8.all badBudget (agreeUdr prm.logBlowup) (DoomedP AP prm) := by
  have hSP' : ∀ τ : PTn, (∀ m, Shaped (VnpP AP prm) (τ.push m) → Shaped (VnpP AP prm) τ) ∧
      (∀ c, Shaped (VnpP AP prm) (τ.pushChal c) → Shaped (VnpP AP prm) τ) := fun τ => by
    simp only [shaped_iff]; exact hSP AP.toAir prm τ
  have hAlt' : ∀ τ : PTn, Shaped (VnpP AP prm) τ →
      ((VnpP AP prm).NextIsProver τ → τ.entries.length % 2 = 0) ∧
      ((VnpP AP prm).NextIsChal τ → τ.entries.length % 2 = 1) := fun τ => by
    simp only [shaped_iff, nextIsProver_iff, nextIsChal_iff]; exact hAlt AP.toAir prm τ
  refine ⟨fun cb hcb => Or.inr (Or.inr hcb), ?_, ?_, ?_⟩
  · -- prover messages
    intro τ m hd hnext
    by_cases hpb : PubBad AP τ
    · exact Or.inr (Or.inl hpb)
    by_cases hs : Shaped (VnpP AP prm) (τ.push m)
    · have hsτ := (hSP' τ).1 m hs
      have hst : StageP AP prm τ := by
        rcases hd with hd | hd | hd
        · exact absurd hsτ hd
        · exact absurd hd hpb
        · exact hd
      have hev := (hAlt' τ hsτ).1 hnext
      refine Or.inr (Or.inr ?_)
      generalize hE : τ.entries.length = E at hev
      match E, hev with
      | 0, _ => exact h0 AP prm hok τ m hpb hs hnext hE hst
      | 2, _ => exact h2 AP prm hok τ m hpb hs hnext hE hst
      | 4, _ => exact h4 AP prm hok τ m hpb hs hnext hE hst
      | 6, _ => exact h6 AP prm hok τ m hpb hs hnext hE hst
      | 8, _ => exact h8 AP prm hok τ m hpb hs hnext hE hst
      | k + 10, _ => exact hML (k + 10) (by omega) AP prm hok τ m hpb hs hnext hE hst
      | 1, h | 3, h | 5, h | 7, h | 9, h => simp at h
    · exact Or.inl hs
  · -- challenges
    intro τ hd hnext
    refine Nat.le_trans (count_mono _ (F := fun c => ¬ PubBad AP τ ∧ Shaped (VnpP AP prm) (τ.pushChal c) ∧
      ¬ StageP AP prm (τ.pushChal c)) ?_) ?_
    · intro c hc
      simp only [DoomedP, _root_.not_or, Classical.not_not] at hc
      exact ⟨hc.2.1, hc.1, hc.2.2⟩
    · by_cases hpb : PubBad AP τ
      · have : count Fp8.all (fun c => ¬ PubBad AP τ ∧ Shaped (VnpP AP prm) (τ.pushChal c) ∧
            ¬ StageP AP prm (τ.pushChal c)) ≤ count Fp8.all (fun _ => False) :=
          count_mono _ fun c h => h.1 hpb
        rw [count_const] at this
        simp at this
        rw [this]; exact Nat.zero_le _
      refine Nat.le_trans (count_mono _ (F := fun c => Shaped (VnpP AP prm) (τ.pushChal c) ∧
        ¬ StageP AP prm (τ.pushChal c)) fun c h => h.2) ?_
      by_cases hsτ : Shaped (VnpP AP prm) τ
      · have hst : StageP AP prm τ := by
          rcases hd with hd | hd | hd
          · exact absurd hsτ hd
          · exact absurd hd hpb
          · exact hd
        have hodd := (hAlt' τ hsτ).2 hnext
        generalize hE : τ.entries.length = E at hodd
        match E, hodd with
        | 1, _ => exact c1 AP prm hok τ hpb hsτ hnext hE hst
        | 3, _ => exact c3 AP prm hok τ hpb hsτ hnext hE hst
        | 5, _ => exact c5 AP prm hok τ hpb hsτ hnext hE hst
        | 7, _ => exact c7 AP prm hok τ hpb hsτ hnext hE hst
        | k + 9, _ => exact cL (k + 9) (by omega) AP prm hok τ hpb hsτ hnext hE hst
        | 0, h | 2, h | 4, h | 6, h | 8, h => simp at h
      · have : count Fp8.all (fun c => Shaped (VnpP AP prm) (τ.pushChal c) ∧
            ¬ StageP AP prm (τ.pushChal c)) ≤ count Fp8.all (fun _ => False) :=
          count_mono _ fun c h => hsτ ((hSP' τ).2 c h.1)
        rw [count_const] at this
        simp at this
        rw [this]; exact Nat.zero_le _
  · -- query phase
    intro τ hd hq hs hg
    have hpb := pubFit_of_global AP prm τ hg
    have hst : StageP AP prm τ := by
      rcases hd with hd | hd | hd
      · exact absurd hs hd
      · exact absurd hd hpb
      · exact hd
    exact hQ AP prm hok τ hst hq hs hg

end ZkFormal.V2.Np
