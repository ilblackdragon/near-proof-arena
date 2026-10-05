import ZkFormal.Bcs.Statements

/-!
# ZkFormal.Bcs.Game2 — the generalised ROM game reduction and budget algebra

Proves the lane-L2 obligations `GameStmt`, `QBAddStmt`, `StepMixStmt`
(`ZkFormal.Bcs.Statements`).

* `inline_queryBoundW` generalises `ZkFormal.inline_queryBound` to hash
  weights `≤ W` (budget `qH·W + qP·NP`).
* `game2` follows `ZkFormal.romSound_of_potential`; the acceptance
  obligation is discharged through `simulate_evalT` on the verifier's run
  (no overflow by `LazyInv`), `simulate_wf` (well-formed final log) and
  `table_length_le` (final log no longer than the tape).
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal

/-! ## Budget algebra -/

theorem qbAdd : QBAddStmt := by
  intro α A w₁ w₂ c₁ c₂ a b hA hB
  induction hA generalizing b with
  | pure x a => exact .pure _ _
  | query q k a hq _ ih =>
    cases hB with
    | query _ _ _ hq2 hk2 =>
    have m1 : c₁ * w₁ q ≤ c₁ * a := Nat.mul_le_mul_left _ hq
    have m2 : c₂ * w₂ q ≤ c₂ * b := Nat.mul_le_mul_left _ hq2
    refine .query q k _ (Nat.add_le_add m1 m2) fun r => ?_
    have h := ih r (b - w₂ q) (hk2 r)
    rw [Nat.mul_sub, Nat.mul_sub] at h
    exact h.mono (by omega)

theorem stepMix : StepMixStmt := by
  intro Φ₁ Φ₂ w₁ w₂ w C₁ C₂ h₁ h₂ hw tbl x hx
  show _ ≤ roRange * ((Φ₁ tbl + Φ₂ tbl) + 1 * w x)
  rw [sum_map_add]
  have h := Nat.add_le_add (h₁ tbl x hx) (h₂ tbl x hx)
  refine Nat.le_trans h ?_
  rw [← Nat.mul_add]
  apply Nat.mul_le_mul_left
  have := hw x
  omega

/-! ## Inlining with weights `≤ W` -/

theorem inline_queryBoundW {S : ChallengeSpec} (P : TreeProver S) (pub : Bytes)
    (w : Bytes → Nat) (W : Nat) (hwW : ∀ x, w x ≤ W) (NP : Nat)
    (hP : ∀ c wit, OracleComp.QueryBound w (P.tree pub c wit) NP) {α : Type} :
    ∀ (A : OracleComp (romSpec S.Witness) α) (qH qP : Nat),
      OracleComp.QueryBound hashWeight A qH → OracleComp.QueryBound proveWeight A qP →
      OracleComp.QueryBound w (inline S P pub A) (qH * W + qP * NP) := by
  classical
  intro A
  induction A with
  | pure a => intro qH qP _ _; exact .pure _ _
  | query q k ih =>
    intro qH qP hH hPr
    cases hH with
    | query _ _ _ hwH hkH =>
    cases hPr with
    | query _ _ _ hwP hkP =>
    cases q with
    | hash x =>
      simp only [hashWeight, proveWeight, Nat.sub_zero] at hwH hkH hkP
      show OracleComp.QueryBound w (OracleComp.query (spec := hashSpec) x fun y => inline S P pub (k y))
        (qH * W + qP * NP)
      have h1 := hwW x
      obtain ⟨m, rfl⟩ : ∃ m, qH = m + 1 := ⟨qH - 1, by omega⟩
      have e : (m + 1) * W = m * W + W := Nat.succ_mul m W
      refine OracleComp.QueryBound.query (spec := hashSpec) (w := w) x _ ((m + 1) * W + qP * NP)
        (by omega) fun y => ?_
      have := ih y m qP (by simpa using hkH y) (hkP y)
      exact this.mono (by omega)
    | prove cb wit =>
      simp only [hashWeight, proveWeight, Nat.sub_zero] at hwP hkH hkP
      simp only [inline]
      have hk : ∀ r, OracleComp.QueryBound w (inline S P pub (k r)) (qH * W + (qP - 1) * NP) :=
        fun r => ih r qH (qP - 1) (hkH r) (hkP r)
      have e : qH * W + qP * NP = NP + (qH * W + (qP - 1) * NP) := by
        obtain ⟨m, rfl⟩ : ∃ m, qP = m + 1 := ⟨qP - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Nat.succ_mul]; omega
      cases S.decodeClaim cb with
      | none => exact (hk []).mono (by rw [e]; exact Nat.le_add_left _ _)
      | some c =>
        simp only
        split
        · rw [e]; exact QueryBound.bind (hP c wit) hk
        · exact (hk []).mono (by rw [e]; exact Nat.le_add_left _ _)

/-! ## The game -/

theorem game2 : GameStmt := by
  intro S L P V pub qH qP NPu NVu hPu hVu w W NPw NVw hwW hPw hVw Φ C M hM hΦ hacc
  intro A hH hPr
  let f : Bytes × Bytes → OracleComp hashSpec (Bytes × Bool) := fun out =>
    OracleComp.bind (V.tree pub out.1 out.2) fun acc => .pure (out.1, acc)
  have hEw : OracleComp.QueryBound w (expt P V pub A) (qH * W + qP * NPw + NVw) := by
    have h := QueryBound.bind (f := f) (b := NVw + 0)
      (inline_queryBoundW P pub w W hwW NPw hPw A qH qP hH hPr)
      fun out => QueryBound.bind (hVw out.1 out.2) fun acc => .pure (out.1, acc) 0
    simpa [expt] using h
  have hEu : OracleComp.QueryBound unitWeight (expt P V pub A) (qH + qP * NPu + NVu) := by
    have h := QueryBound.bind (f := f) (b := NVu + 0)
      (inline_queryBoundW P pub unitWeight 1 (fun _ => Nat.le_refl 1) NPu hPu A qH qP hH hPr)
      fun out => QueryBound.bind (hVu out.1 out.2) fun acc => .pure (out.1, acc) 0
    simpa [expt] using h
  refine prLE_of_potential hΦ hEw _ [] false _ M hM ?_
  intro t ht hwin
  rw [romWins_iff] at hwin
  obtain ⟨k', _, hinv⟩ := LazyInv.simulate hEu (LazyInv.init t) (by omega)
  have hov := hinv.2.1
  have hlen := table_length_le hEu (LazyRO.init t)
  have hwf := simulate_wf (expt P V pub A) (LazyRO.init t) TableWF.nil
  simp only at hwin
  rcases hwin with hwin | ⟨hacc', hnl⟩
  · rw [hov] at hwin; cases hwin
  · rw [simulate_expt] at hacc' hnl hov hlen hwf
    simp only at hacc' hnl hov hlen hwf
    have hev := simulate_evalT _ _ hov
    rw [hacc'] at hev
    have := hacc _ _ _ hwf (by simpa [LazyRO.init] using hlen) hev hnl
    show M ≤ Φ (finalTable (expt P V pub A) (LazyRO.init t))
    unfold finalTable
    rw [simulate_expt]
    exact this

end ZkFormal.Bcs
