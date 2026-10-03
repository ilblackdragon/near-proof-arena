import ZkFormal.Bcs.Statements

/-!
# ZkFormal.Bcs.Compose — the compiled verifier is ROM-sound (lane L2 top theorem)

`bcs_romSound`: for any IOP (`IopSpec`) over any binding commitment scheme,
any verifier tree whose acceptance certifies `AcceptsIn` on its final oracle
log, and any honest prover tree, the judge's `RomSound` holds with the
explicit bound `bcsNum … / 2^(256·K)`, given the round-by-round facts of the
IOP (`hinit`, `hmsg`, `hround`, `hquery`: lane L3's `RbrFacts`, transported
to byte transcripts).  Proved from the sublemma statements of
`Bcs.Statements` (taken as hypotheses).

The potential is
`R^(K-1)·badPot RoundBad + queryPot Good + R^(K-2)·pairPot + R^(K-1)·Φ_inv`,
threshold `R^K` (`R = 2^256`, `K` = number of query chunks).
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal

section
variable {cs : CommitScheme} (iop : IopSpec cs) (Doomed : PT cs → Prop) (ctx : Bytes)

theorem chalMsg_whq_inj {d d' : Bytes} (h : whq (chalMsg d) 0 = whq (chalMsg d') 0) : d = d' := by
  have := (whq_inj (by omega) (by omega) h).1
  simp only [chalMsg, List.cons.injEq] at this
  exact this.2

/-- Per query, at most `B` answers are commit-phase bad. -/
theorem roundBad_count (B : Nat)
    (hround : ∀ τ : PT cs, Doomed τ →
      count (List.range roRange) (fun v => ¬ Doomed (τ.push (.chal (LazyRO.answer v)))) ≤ B)
    (tbl : Table) (x : Bytes) :
    count (List.range roRange) (fun v => RoundBad iop Doomed ctx tbl x (LazyRO.answer v)) ≤ B * unitWeight x := by
  classical
  simp only [unitWeight, Nat.mul_one]
  by_cases hx : ∃ d τ, x = whq (chalMsg d) 0 ∧ extPT iop ctx tbl d = some τ ∧ Doomed τ
  · obtain ⟨d, τ, rfl, hτ, hd⟩ := hx
    refine Nat.le_trans (count_mono _ fun v hv => ?_) (hround τ hd)
    obtain ⟨d', τ', hx', hτ', _, hnd⟩ := hv
    have := chalMsg_whq_inj hx'; subst this
    rw [hτ] at hτ'; cases hτ'
    exact hnd
  · refine Nat.le_trans (count_mono _ (F := fun _ => False) fun v hv => ?_) (by simp [count])
    obtain ⟨d', τ', hx', hτ', hd', _⟩ := hv
    exact hx ⟨d', τ', hx', hτ', hd'⟩

theorem good_count (g : Nat → Nat)
    (hquery : ∀ (τ : PT cs) (j : Nat), Doomed τ →
      count (List.range roRange) (fun v => ∀ pt ∈ iop.points τ.view j (LazyRO.answer v), Pass iop τ pt) ≤ g j)
    (hist : Table) (p : Bytes) (j : Nat) :
    count (List.range roRange) (fun v => Good iop Doomed ctx hist p j (LazyRO.answer v)) ≤ g j := by
  classical
  by_cases hx : ∃ τ, extPT iop ctx hist p = some τ ∧ Doomed τ
  · obtain ⟨τ, hτ, hd⟩ := hx
    refine Nat.le_trans (count_mono _ fun v hv => ?_) (hquery τ j hd)
    obtain ⟨τ', hτ', _, hp⟩ := hv
    rw [hτ] at hτ'; cases hτ'
    exact hp
  · refine Nat.le_trans (count_mono _ (F := fun _ => False) fun v hv => ?_) (by simp [count])
    obtain ⟨τ', hτ', hd', _⟩ := hv
    exact hx ⟨τ', hτ', hd'⟩

end

theorem stepBound_smul' {Φ : Table → Nat} {w : Bytes → Nat} {C : Nat} (k : Nat) (h : StepBound Φ w C) :
    StepBound (fun t => k * Φ t) w (k * C) := StepBound.smul k h

theorem badPot_nil (Bad : Table → Bytes → Bytes → Prop) : badPot Bad [] = 0 := by
  unfold badPot; simp [BadHist]

theorem pairPot_nil (k : Nat) (enc : Bytes → Nat → Bytes) (dec : Bytes → Option (Bytes × Nat)) (N : Nat) :
    pairPot k enc dec N [] = 0 := by
  unfold pairPot oldest pairSum; simp [touched]

/-- **ROM soundness of the BCS-compiled verifier** (generic `compile_romSound`). -/
theorem bcs_romSound (hGame : GameStmt) (hQB : QBAddStmt) (hMix : StepMixStmt) (hInv : InvPotStmt)
    {cs : CommitScheme} (hbind : cs.Binding) (hroot : cs.Rooted)
    (iop : IopSpec cs) (hK : 2 ≤ iop.numChunks) (hK' : iop.numChunks ≤ 2 ^ 32)
    (Doomed : PT cs → Prop) (ctx : Bytes)
    {S : ChallengeSpec} (L : Bytes → Prop) (P : TreeProver S) (V : TreeVerifier) (pub : Bytes)
    (hV : ∀ tbl cb pb, evalT tbl (V.tree pub cb pb) = some true → AcceptsIn iop tbl ctx cb)
    (hinit : ∀ cb, ¬ L cb → Doomed ⟨cb, []⟩)
    (hmsg : ∀ τ roots raw os, Doomed τ → Doomed (τ.push (.msg roots raw os)))
    (B : Nat) (hround : ∀ τ : PT cs, Doomed τ →
      count (List.range roRange) (fun v => ¬ Doomed (τ.push (.chal (LazyRO.answer v)))) ≤ B)
    (g : Nat → Nat) (hquery : ∀ (τ : PT cs) (j : Nat), Doomed τ →
      count (List.range roRange) (fun v => ∀ pt ∈ iop.points τ.view j (LazyRO.answer v), Pass iop τ pt) ≤ g j)
    (qH qP NPu NVu NPq NVq : Nat) (hN : qH + qP * NPu + NVu ≤ 2 ^ 100)
    (hPu : ∀ c wit, OracleComp.QueryBound unitWeight (P.tree pub c wit) NPu)
    (hVu : ∀ cb pb, OracleComp.QueryBound unitWeight (V.tree pub cb pb) NVu)
    (hPq : ∀ c wit, OracleComp.QueryBound (qWeight chunkDec) (P.tree pub c wit) NPq)
    (hVq : ∀ cb pb, OracleComp.QueryBound (qWeight chunkDec) (V.tree pub cb pb) NVq) :
    RomSound S L V.toVerifier P.toProver pub qH qP (qH + qP * NPu + NVu)
      (bcsNum iop.numChunks B ((List.range iop.numChunks).map g).prod qH qP NPu NVu NPq NVq)
      (roRange ^ iop.numChunks) := by
  classical
  -- notation
  let G := ((List.range iop.numChunks).map g).prod
  obtain ⟨Φi, hΦi, hΦi0, hΦiM⟩ := hInv (qH + qP * NPu + NVu) hN
  let A := roRange ^ (iop.numChunks - 1) * (B + 1024) + roRange ^ (iop.numChunks - 2) * (2 * (qH + qP * NPu + NVu))
  -- the four potentials
  let Φ1 : Table → Nat := fun t => roRange ^ (iop.numChunks - 1) * badPot (RoundBad iop Doomed ctx) t
  let Φ2 : Table → Nat := queryPot iop.numChunks chunkQ chunkDec (Good iop Doomed ctx) g
  let Φ3 : Table → Nat := fun t => roRange ^ (iop.numChunks - 2) * pairPot 2 whq whDec (qH + qP * NPu + NVu) t
  let Φ4 : Table → Nat := fun t => roRange ^ (iop.numChunks - 1) * Φi t
  have hdecC : ∀ p j, j < iop.numChunks → chunkDec (chunkQ p j) = some (p, j) :=
    fun p j hj => chunkDec_chunkQ p j (by omega)
  have h1 : StepBound Φ1 unitWeight (roRange ^ (iop.numChunks - 1) * B) :=
    StepBound.smul _ (badPot_step _ unitWeight B (roundBad_count iop Doomed ctx B hround))
  have h2 : StepBound Φ2 (qWeight chunkDec) G :=
    product_step iop.numChunks chunkQ chunkDec hdecC (Good iop Doomed ctx) g (good_count iop Doomed ctx g hquery)
  have h3 : StepBound Φ3 unitWeight (roRange ^ (iop.numChunks - 2) * (2 * (qH + qP * NPu + NVu))) :=
    StepBound.smul _ (pairPot_step 2 whq whDec (fun m j hj => whDec_whq m j hj) (qH + qP * NPu + NVu))
  have h4 : StepBound Φ4 unitWeight (roRange ^ (iop.numChunks - 1) * 1024) := StepBound.smul _ hΦi
  let w : Bytes → Nat := fun x => A * unitWeight x + G * qWeight chunkDec x
  have h13 : StepBound (fun t => Φ1 t + Φ3 t) (fun _ => roRange ^ (iop.numChunks - 1) * B + roRange ^ (iop.numChunks - 2) * (2 * (qH + qP * NPu + NVu))) 1 :=
    hMix Φ1 Φ3 unitWeight unitWeight _ _ _ h1 h3 (fun x => by simp [unitWeight])
  have h134 : StepBound (fun t => (Φ1 t + Φ3 t) + Φ4 t) (fun _ => A) 1 :=
    hMix _ Φ4 _ unitWeight _ 1 _ h13 h4 (fun x => by
      simp only [unitWeight, Nat.one_mul, Nat.mul_one, A, Nat.mul_add]; omega)
  have hall : StepBound (fun t => ((Φ1 t + Φ3 t) + Φ4 t) + Φ2 t) w 1 :=
    hMix _ Φ2 _ (qWeight chunkDec) w 1 G h134 h2 (fun x => by simp [w, unitWeight])
  have hwW : ∀ x, w x ≤ A + G := by
    intro x; simp only [w, unitWeight, Nat.mul_one]
    have : qWeight chunkDec x ≤ 1 := by unfold qWeight; split <;> omega
    have := Nat.mul_le_mul_left G this
    omega
  have hRpos : 0 < roRange := by rw [roRange_eq]; exact Nat.pow_pos (by decide)
  have hgame := hGame L P V pub qH qP NPu NVu hPu hVu w (A + G) (A * NPu + G * NPq) (A * NVu + G * NVq) hwW
    (fun c wit => hQB _ unitWeight (qWeight chunkDec) A G _ _ (hPu c wit) (hPq c wit))
    (fun cb pb => hQB _ unitWeight (qWeight chunkDec) A G _ _ (hVu cb pb) (hVq cb pb))
    _ 1 (roRange ^ iop.numChunks) (Nat.pow_pos hRpos) hall ?acc
  case acc =>
    intro tbl cb pb wf hlen hev hL
    have hpow1 : roRange ^ (iop.numChunks - 1) * roRange = roRange ^ iop.numChunks := by rw [← Nat.pow_succ]; congr 1; omega
    have hpow2 : roRange ^ (iop.numChunks - 2) * roRange ^ 2 = roRange ^ iop.numChunks := by rw [← Nat.pow_add]; congr 1; omega
    rcases accept_imp_event_log hbind hroot hmsg wf (hinit cb hL) (hV tbl cb pb hev) with
      h | h | h | h
    · -- commit phase
      have : roRange ≤ badPot (RoundBad iop Doomed ctx) tbl := by
        unfold badPot; rw [if_pos h]; exact Nat.le_refl _
      have := Nat.mul_le_mul_left (roRange ^ (iop.numChunks - 1)) this
      simp only [Φ1, Φ2, Φ3, Φ4] at *
      omega
    · -- query phase
      have := querySuccess_pot iop.numChunks (by omega) chunkQ chunkDec hdecC (Good iop Doomed ctx) g tbl h
      simp only [Φ1, Φ2, Φ3, Φ4] at *
      omega
    · -- wide collision
      have := wideCollision_pot 2 (by omega) whq whDec (fun m j hj => whDec_whq m j hj) (qH + qP * NPu + NVu) tbl hlen h
      have := Nat.mul_le_mul_left (roRange ^ (iop.numChunks - 2)) this
      simp only [Φ1, Φ2, Φ3, Φ4] at *
      omega
    · -- inversion
      have := Nat.mul_le_mul_left (roRange ^ (iop.numChunks - 1)) (hΦiM tbl hlen h)
      simp only [Φ1, Φ2, Φ3, Φ4] at *
      omega
  have h0 : ((Φ1 [] + Φ3 []) + Φ4 []) + Φ2 [] = 0 := by
    simp only [Φ1, Φ2, Φ3, Φ4, badPot_nil, pairPot_nil, hΦi0, Nat.mul_zero]
    rfl
  simp only [h0, Nat.zero_add, Nat.one_mul] at hgame
  have e : bcsNum iop.numChunks B ((List.range iop.numChunks).map g).prod qH qP NPu NVu NPq NVq =
      qH * (A + G) + qP * (A * NPu + G * NPq) + (A * NVu + G * NVq) := rfl
  rw [e]
  exact hgame

end ZkFormal.Bcs
