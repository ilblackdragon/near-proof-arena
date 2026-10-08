import ZkFormal.NearV3.Candidates.ProcActualRoundTransition
import ZkFormal.NearV3.Candidates.ProcBucketSize
namespace ZkFormal.NearV3.Candidates.ProcActualPreparedReplay
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
open ProcActualReplayRound ProcActualRoundTransition

/-- Prepared native processing discharges every per-round guard and invariant
needed for the full actual outer replay loop. Initial alignment remains explicit. -/
theorem prepared_replay (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (s : Acc)
    (ha : Aligned (NearSpecV3.leWords sp.seed) cv s
      (ProcActualInput.initial (ProcPreparedSequence.input sp prev)) cv.size) :
    ∃out last,forIn rs s (step (ProcPreparedSequence.input sp prev) cv (NearSpecV3.leWords sp.seed))=.ok out ∧
      Aligned (NearSpecV3.leWords sp.seed) cv out st last := by
  let I := ProcPreparedSequence.input sp prev
  have hreq : convRaw I.p I.ids.length I.raw=ProcActualConversionExact.view cv := by
    simpa [ProcActualConversionExact.view] using
      (ProcActualConversionExact.loop_view I I.raw #[] cv hcv).symm
  have hlen : (convRaw I.p I.ids.length I.raw).length=cv.size := by
    rw [hreq]; simp [ProcActualConversionExact.view]
  obtain ⟨last,ht⟩ := ProcModelBatchTrace.process_trace I.ids.length I.allowed
    (convRaw I.p I.ids.length I.raw) (ProcActualInput.initial I) st _ rs hproc
  rw [hlen,hreq] at ht
  have hgood := ProcPreparedRequestGood.converted_good I.p I.ids.length I.raw hs.params
  have hv := ProcShufflePointers.process_pointers I.ids.length I.allowed
    (convRaw I.p I.ids.length I.raw) (fun q hq=>Nat.le_of_lt (hgood q hq).1) _ st _ rs hproc
  have htags := ProcActualBucketGuards.process_tags I.ids.length I.allowed _ _ st _ rs hproc
  have hb := ProcBucketSize.process_bounds I.ids.length I.allowed _ hgood _ st _ rs
    (ProcActualInput.prepared_ready sp hs prev) hproc
  have hraw := (ProcPreparedSequence.input_bounds sp prev hs).2.2
  change I.raw.length≤4096 at hraw
  have hc : (convRaw I.p I.ids.length I.raw).length≤I.raw.length := List.length_filterMap_le _ _
  have hsize : ∀rd∈rs,1≤rd.bucket.length ∧ rd.bucket.length<16384 := by
    intro rd hr
    have hh := hb rd hr
    omega
  rw [hreq] at hv
  obtain ⟨out,ho,he⟩ := trace_replay I cv hcv (NearSpecV3.leWords sp.seed)
    (ProcActualInput.initial I) cv.size rs st last ht (ProcActualAllowanceShape.initial_shape I)
    (fun rd hr => (hv rd hr).2) hsize htags s ha
  exact ⟨out,last,ho,he⟩
end ZkFormal.NearV3.Candidates.ProcActualPreparedReplay
