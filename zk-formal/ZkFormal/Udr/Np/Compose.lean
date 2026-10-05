import ZkFormal.Udr.Np.Statements

/-!
# ZkFormal.Udr.Np.Compose — `RbrFacts` of np-udr-stark from the obligations
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

theorem rbrWith_of (hSP : ShapedPrefixStmt) (hAlt : ScheduleAltStmt)
    (h0 : Msg0Stmt) (h2 : Msg2Stmt) (h4 : Msg4Stmt) (h6 : Msg6Stmt) (h8 : Msg8Stmt)
    (hML : MsgLateStmt) (c1 : Chal1Stmt) (c3 : Chal3Stmt) (c5 : Chal5Stmt) (c7 : Chal7Stmt)
    (cL : ChalLateStmt) (hQ : QueryStmt) (A : Air) (prm : Params) (hok : NpOk A prm) :
    RbrWith (Vnp A prm) (AirLang Fp A) Fp8.all badBudget (agreeUdr prm.logBlowup) (Doomed A prm) := by
  refine ⟨fun cb hcb => Or.inr hcb, ?_, ?_, ?_⟩
  · -- prover messages
    intro τ m hd hnext
    by_cases hs : Shaped (Vnp A prm) (τ.push m)
    · have hsτ := (hSP A prm τ).1 m hs
      have hst : Stage A prm τ := hd.resolve_left (fun h => h hsτ)
      have hev := (hAlt A prm τ hsτ).1 hnext
      refine Or.inr ?_
      generalize hE : τ.entries.length = E at hev
      match E, hev with
      | 0, _ => exact h0 A prm hok τ m hs hnext hE hst
      | 2, _ => exact h2 A prm hok τ m hs hnext hE hst
      | 4, _ => exact h4 A prm hok τ m hs hnext hE hst
      | 6, _ => exact h6 A prm hok τ m hs hnext hE hst
      | 8, _ => exact h8 A prm hok τ m hs hnext hE hst
      | k + 10, _ => exact hML (k + 10) (by omega) A prm hok τ m hs hnext hE hst
      | 1, h | 3, h | 5, h | 7, h | 9, h => simp at h
    · exact Or.inl hs
  · -- challenges
    intro τ hd hnext
    refine Nat.le_trans (count_mono _ (F := fun c => Shaped (Vnp A prm) (τ.pushChal c) ∧
      ¬ Stage A prm (τ.pushChal c)) ?_) ?_
    · intro c hc
      simp only [Doomed, _root_.not_or, Classical.not_not] at hc
      exact hc
    · by_cases hsτ : Shaped (Vnp A prm) τ
      · have hst : Stage A prm τ := hd.resolve_left (fun h => h hsτ)
        have hodd := (hAlt A prm τ hsτ).2 hnext
        generalize hE : τ.entries.length = E at hodd
        match E, hodd with
        | 1, _ => exact c1 A prm hok τ hsτ hnext hE hst
        | 3, _ => exact c3 A prm hok τ hsτ hnext hE hst
        | 5, _ => exact c5 A prm hok τ hsτ hnext hE hst
        | 7, _ => exact c7 A prm hok τ hsτ hnext hE hst
        | k + 9, _ => exact cL (k + 9) (by omega) A prm hok τ hsτ hnext hE hst
        | 0, h | 2, h | 4, h | 6, h | 8, h => simp at h
      · have : count Fp8.all (fun c => Shaped (Vnp A prm) (τ.pushChal c) ∧
            ¬ Stage A prm (τ.pushChal c)) ≤ count Fp8.all (fun _ => False) :=
          count_mono _ fun c h => hsτ ((hSP A prm τ).2 c h.1)
        rw [count_const] at this
        simp at this
        rw [this]; exact Nat.zero_le _
  · -- query phase
    intro τ hd hq hs hg
    exact hQ A prm hok τ (hd.resolve_left fun h => h hs) hq hs hg

theorem rbr_of (hSP : ShapedPrefixStmt) (hAlt : ScheduleAltStmt)
    (h0 : Msg0Stmt) (h2 : Msg2Stmt) (h4 : Msg4Stmt) (h6 : Msg6Stmt) (h8 : Msg8Stmt)
    (hML : MsgLateStmt) (c1 : Chal1Stmt) (c3 : Chal3Stmt) (c5 : Chal5Stmt) (c7 : Chal7Stmt)
    (cL : ChalLateStmt) (hQ : QueryStmt) (A : Air) (prm : Params) (hok : NpOk A prm) :
    RbrFacts (Vnp A prm) (AirLang Fp A) Fp8.all badBudget (agreeUdr prm.logBlowup) :=
  ⟨Doomed A prm, rbrWith_of hSP hAlt h0 h2 h4 h6 h8 hML c1 c3 c5 c7 cL hQ A prm hok⟩

end ZkFormal.Udr.Np
