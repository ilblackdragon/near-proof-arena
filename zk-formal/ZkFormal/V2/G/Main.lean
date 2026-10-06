import ZkFormal.V2.G.Query

/-!
# ZkFormal.V2.G.Main — round-by-round soundness of np-udr-stark-v2 with `auxGroup ∈ {1,2,3}`

`rbrWithPg`: for every v2 AIR `AP` and parameters with `NpOkPg AP prm`
(`prm = pg g = {Params.default with auxGroup := g}`, `1 ≤ g ≤ 3`, v1's constraint-count and
bus-count bounds, and `AirP.wf`), the IOP verifier `Iop.verifierP Fp Fp8 AP prm` has
round-by-round soundness for `AirLangP AP` with v1's budgets (`2^36` bad challenges per
round, `agreeUdr` passing query positions).  `NpOkP AP prm → NpOkPg AP prm`
(`npOkPg_of_npOkP`), so this extends `V2.Np.rbrWithP`.
-/

namespace ZkFormal.V2.G

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2 ZkFormal.V2.Np

theorem rbrWithPg_of (hSP : ShapedPrefixStmt) (hAlt : ScheduleAltStmt)
    (h0 : MsgAtPg 0) (h2 : MsgAtPg 2) (h4 : MsgAtPg 4) (h6 : MsgAtPg 6) (h8 : MsgAtPg 8)
    (hML : ∀ k, 10 ≤ k → MsgAtPg k) (c1 : ChalAtPg 1) (c3 : ChalAtPg 3) (c5 : ChalAtPg 5) (c7 : ChalAtPg 7)
    (cL : ∀ k, 9 ≤ k → ChalAtPg k) (hQ : QueryStmtPg) (AP : AirP) (prm : Params) (hok : NpOkPg AP prm) :
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

theorem rbrWithPg (AP : AirP) (prm : Params) (hok : NpOkPg AP prm) :
    RbrWith (VnpP AP prm) (AirLangP AP) Fp8.all badBudget (agreeUdr prm.logBlowup) (DoomedP AP prm) :=
  rbrWithPg_of shapedPrefix scheduleAlt msg0P msg2P msg4P msg6P msg8P msgLateP chal1P chal3P chal5P chal7P
    chalLateP queryP AP prm hok

theorem rbrFactsPg (AP : AirP) (prm : Params) (hok : NpOkPg AP prm) :
    RbrFacts (VnpP AP prm) (AirLangP AP) Fp8.all badBudget (agreeUdr prm.logBlowup) :=
  ⟨DoomedP AP prm, rbrWithPg AP prm hok⟩

end ZkFormal.V2.G
