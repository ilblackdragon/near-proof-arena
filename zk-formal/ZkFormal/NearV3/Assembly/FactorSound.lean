import ZkFormal.NearV3.Assembly.SourceComplete
import ZkFormal.NearV3.Assembly.ImplicitComplete
import ZkFormal.NearV3.Assembly.ClaimFacts

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem GoodV3.checkD0 {B cb k hint p x} (g : GoodV3 B cb k hint p x) :
    checkD0 cb (witnessOfV3 k x) = .ok () := by
  have hg := prepD0_guards g.prepared g.walk
  obtain ⟨m, last, hm, hi, hh⟩ := g.executions
  have hs := g.source.loop
  have him := hi.witness_loop
  have hdfile := V3.decodeWitnessFile_encode _ g.shape
  have hdsw := V3.decodeStateWitness_encode _ g.shape
  have hsize : lenT (V3.encodeSW (stateWitnessOfV3 k x)) ≤ 8388608 := by
    simpa only [ReexecV3D0.lenT_eq'] using g.witnessBytes
  have hbase := g.mainStoreBytes
  have hids := g.receiptIds
  have hcount := g.source.dictionaryCount
  have htx := g.mainTxRoot
  have hcong := g.ownCongestion
  have hw := g.walk
  clear g
  unfold walkD0 at hw
  repeat' (first
    | (have h := hw; clear hw; obtain ⟨_, _, hw⟩ := bind_ok h; clear h)
    | (split at hw)
    | (dsimp only at hw))
  all_goals try (cases hw; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hw
    subst hw
    cases hg
    rcases hm with ⟨hb, hprev, hbuffer, hpre, hroot, hrun, hpost⟩
    obtain ⟨value, hfind, hshards⟩ := hbuffer
    cases hh
    simp_all only [pure, Except.pure, Except.ok.injEq, Option.bind_some,
      beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    unfold NearSpecV3.checkD0 witnessOfV3
    simp only [hdfile, hdsw, hsize, List.isEmpty_nil, check, bind, Except.bind,
      pure, Except.pure, ↓reduceIte]
    unfold checkedSourceBlock checkedSourceSlot at hs
    simp only [stateWitnessOfV3,
      check, bind, Except.bind, pure, Except.pure, beq_iff_eq, ↓reduceIte] at hs
    unfold checkedImplicitStep at him
    simp only [stateWitnessOfV3, ExtV3.transition, check, bind, Except.bind,
      pure, Except.pure, beq_iff_eq, ↓reduceIte] at him
    dsimp only [MainExecutionV3.ctx] at hrun
    simp only [*,
      stateWitnessOfV3, ExtV3.transition, MainExecutionV3.ctx,
      Except.mapError, check, bind, Except.bind, pure, Except.pure,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.isEmpty_nil,
      List.length_map, List.length_zipIdx, List.length_nil, List.nil_append,
      ↓reduceIte, true_and, and_true]
    repeat' (
      conv =>
        lhs
        pattern (List.findIdx? _ _)
        tactic => assumption
      simp only [*, Except.mapError, check, bind, Except.bind, pure, Except.pure,
        ↓reduceIte, beq_iff_eq, Bool.and_eq_true, true_and, and_true])
    conv =>
      lhs
      pattern (forIn _ _ _)
      tactic => assumption
    simp only [*, stateWitnessOfV3, ExtV3.transition, MainExecutionV3.ctx,
      Except.mapError, check, bind, Except.bind, pure, Except.pure,
      ↓reduceIte, beq_iff_eq, Bool.and_eq_true, true_and, and_true]


theorem GoodV3.checkD0a {B cb k hint p x} (g : GoodV3 B cb k hint p x) :
    NearSpecV3.checkD0a B cb (witnessOfV3 k x) = .ok () := by
  obtain ⟨h1, h2, h0f, h7, h8⟩ := g.amendments
  simp only [NearSpecV3.checkD0a, g.checkD0, h1, h2, h0f, h7, h8,
    check, bind, Except.bind, pure, Except.pure, ↓reduceIte]

/-- Semantic reconstructed views imply the unchanged amended native checker. -/
theorem factorSound : FactorSound := fun _ _ _ _ _ _ g => g.checkD0a

end ZkFormal.NearV3.Assembly
