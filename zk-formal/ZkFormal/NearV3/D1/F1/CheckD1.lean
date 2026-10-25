import ZkFormal.NearV3.D1.F1.WitnessCodec
import ZkFormal.NearV3.D1.F1.ClaimGuards

/-!
# `ZkFormal.NearV3.D1.F1.CheckD1` — `checkD1` accepts the extracted D1 witness (`F1`)

Lane `v3-d1-phase2`, item F1.  D0a's `GoodV3.checkD0`
(`ZkFormal/NearV3/Assembly/FactorSound.lean`) for the frozen D1 checker, with the D1 deltas
discharged from `GoodD1Core`: **`checkD1_witnessOfD1`**, `checkD1 cb (witnessOfD1 k x h) = .ok ()`.

The witness decoding is the codec (`F1/WitnessCodec`) and the claim-level gates are
`F1/ClaimGuards`; the execution, source, run and header fields of `GoodD1Core` then discharge
the remaining checks of `checkD1` (`applyNewChunkD1` on the D1 state witness, the source loop,
the implicit run and the endorsed header).
-/

namespace ZkFormal.NearV3.D1.F1

open NearSpec NearSpecV3 ZkFormal.NearV3.Assembly ZkFormal.NearV3.D1 ZkFormal.NearV3.Sched

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- **`checkD1` accepts the extracted witness.**  `GoodD1Core` gives the codec facts, the
claim guards and every remaining check that `checkD1` runs on `witnessOfD1 k x h`. -/
theorem checkD1_witnessOfD1 {cb : NearSpec.Bytes} {k : NearSpecV3.WalkD0}
    {h : ZkFormal.NearV3.D1.HintD1} {p : ZkFormal.NearV3.D1.Public.PrepD1}
    {x : ZkFormal.NearV3.Assembly.ExtV3}
    {ts nts : List NearSpecV3.Tx} (g : ZkFormal.NearV3.D1.GoodD1Core cb k h p x ts nts) :
    NearSpecV3.checkD1 cb (ZkFormal.NearV3.D1.witnessOfD1 k x h) = .ok () := by
  have hg := claimGuards_of_prepD1 g.prepared g.walk
  have hcodec := witnessOfD1_codec g
  obtain ⟨m, last, hm, hi, hh⟩ := g.executions
  have hs := g.source.loop
  have him := hi.witness_loop
  have hdfile := hcodec.file
  have hdsw := hcodec.state
  have hsize : lenT (encodeSWD1 (stateWitnessOfV3 k x) h.txs h.newTxs) ≤ 8388608 := by
    simpa only [ReexecV3D0.lenT_eq'] using hcodec.size
  have hbase := g.mainStoreBytes
  have hcount := g.source.dictionaryCount
  have htx := g.txRoot
  have htxv := g.txValid
  have hnsz := g.newSize
  obtain ⟨hcong1, hcong2, hcong3⟩ := g.ownCongestion
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
    rcases hm with ⟨hb, hprev, hbuffer, hpre, hroot, hrun, hpost, hdistinct⟩
    obtain ⟨value, hfind, hshards⟩ := hbuffer
    cases hh
    simp_all only [pure, Except.pure, Except.ok.injEq, Option.bind_some, beq_iff_eq,
      Bool.and_eq_true]
    -- `checkD1` is definitionally `(checkD1CoreObs …).map fun _ => ()` (the output-returning checker
    -- projected to its verdict, `NearSpecV3.ChunkValidationD1`), so the pipeline to reduce is the
    -- observable one and the projection's equation closes the goal.
    unfold NearSpecV3.checkD1 NearSpecV3.checkD1CoreObs
    simp only [hdfile, hdsw, hsize, List.isEmpty_nil, check, bind, Except.bind,
      pure, Except.pure, Except.map.eq_def, ↓reduceIte]
    unfold ZkFormal.NearV3.checkedSourceBlock ZkFormal.NearV3.checkedSourceSlot at hs
    simp only [check, bind, Except.bind, pure, Except.pure, beq_iff_eq] at hs
    unfold checkedImplicitStep at him
    simp only [stateWitnessOfV3, ExtV3.transition, check, bind, Except.bind,
      pure, Except.pure, beq_iff_eq] at him
    dsimp only [MainExecutionD1.ctx] at hrun
    simp only [*, stateWitnessD1Of, stateWitnessOfV3, ExtV3.transition, Except.mapError,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.length_map, List.length_zipIdx,
      ↓reduceIte, and_true]
    repeat' (
      conv =>
        lhs
        pattern (List.findIdx? _ _)
        tactic => assumption
      simp only [*, ↓reduceIte, and_true])
    conv =>
      lhs
      pattern (forIn _ _ _)
      tactic => assumption
    simp only [*, ↓reduceIte]

end ZkFormal.NearV3.D1.F1
