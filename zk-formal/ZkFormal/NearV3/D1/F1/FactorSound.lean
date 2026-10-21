import ZkFormal.NearV3.D1.Link.Statements
import ZkFormal.NearV3.D1.F1.CheckD1

/-!
# `ZkFormal.NearV3.D1.F1.FactorSound` — F1: `FactorSoundD1 B0`, proved

Lane `v3-d1-phase2`, item F1.  **`factorSoundD1_B0 : FactorSoundD1 NearSpecV3.B0`**: the D1
semantic views (`GoodD1Core`, every condition of the D1a checker except A7) together with the
A7 conjunct give `RelD1a B0 cb (witnessOfD1 k x h)`.

`RelD1a B cb w` is `RelD1 cb w ∧ a1 cb ∧ a2D1 cb w ∧ canon0fD1 cb w ∧ a7D1 B cb w ∧ a8 cb ∧
a9D1 W0 cb w ∧ a10D1 Dp0 cb w ∧ a12 cb ∧ t1 NT0 w` (`NearSpecV3/ChunkValidationD1a.lean`).
`RelD1` (the frozen D1 checker accepts the extracted witness) is `F1.CheckD1`; the domain
conjuncts are the `GoodD1Core` fields, rewritten through the witness codec (`F1.WitnessCodec`),
exactly as D0a's `GoodV3.amendments` (`Assembly/FactorSound.lean`) does for `checkD0a`.
-/

namespace ZkFormal.NearV3.D1.Link

open NearSpec NearSpecV3 ZkFormal.NearV3.Assembly ZkFormal.NearV3.D1

/-- **F1: the semantic views and the A7 conjunct give the relation.**  `RelD1` is
`checkD1_witnessOfD1`; A7ᴰ¹ is the hypothesis; the eight domain conjuncts are the
`GoodD1Core` fields, rewritten through the codec facts of `witnessOfD1_codec`. -/
theorem factorSoundD1_B0 : FactorSoundD1 NearSpecV3.B0 := by
  intro cb k h p x ts nts g h7
  -- the D1 witness codec: `witnessOfD1` decodes to the D1 views
  have hcodec := F1.witnessOfD1_codec g
  have hdec : decodeWD1 (witnessOfD1 k x h) = .ok (stateWitnessD1Of k x ts nts) := hcodec.decode
  -- the frozen D1 checker accepts the extracted witness (the claim-level checks of
  -- `prepD1` are discharged inside `F1.CheckD1`)
  have hrel : checkD1 cb (witnessOfD1 k x h) = .ok () := F1.checkD1_witnessOfD1 g
  unfold NearSpecV3.RelD1a
  refine ⟨?_, ?_, ?_, ?_, h7, ?_, ?_, ?_, ?_, ?_⟩
  · -- `RelD1`
    simp only [NearSpecV3.RelD1, NearSpecV3.acceptsD1, hrel]
  · -- A1 (`c.gas_limit`)
    simpa [NearSpecV3.a1, g.walk] using g.gasLimit
  · -- A2ᴰ¹ (`w.proof_routing`)
    simp only [NearSpecV3.a2D1, g.walk, hdec]
    exact List.all_eq_true.mpr fun e he =>
      List.all_eq_true.mpr fun r hr => beq_iff_eq.mpr (g.source.routing e he r hr)
  · -- Canon0fᴰ¹ (`e.sched_canonical`)
    simp only [NearSpecV3.canon0fD1, g.walk, hdec]
    exact g.canonicalScheduler
  · -- A8 (`c.bw_requests`)
    simp only [NearSpecV3.a8, g.walk]
    exact List.all_eq_true.mpr fun b hb =>
      List.all_eq_true.mpr fun p hp => decide_eq_true (g.distinctRequests b hb p.1 p.2 hp)
  · -- A9ᴰ¹ (`e.chacha_words`)
    simpa [NearSpecV3.a9D1] using g.chachaWords
  · -- A10ᴰ¹ (`w.path_depth`)
    simp only [NearSpecV3.a10D1, g.walk, hdec]
    exact List.all_eq_true.mpr fun e he => decide_eq_true (g.pathDepth e he)
  · -- A12 (`c.layout_wf`)
    simp only [NearSpecV3.a12, g.walk, g.layoutWf, beq_self_eq_true]
  · -- T1 (`w.tx_count`)
    simp only [NearSpecV3.t1, hdec]
    exact decide_eq_true g.txCount

end ZkFormal.NearV3.D1.Link
