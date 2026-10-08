import ZkFormal.NearV3.Candidates.ProcActualBatchPush
namespace ZkFormal.NearV3.Candidates.ProcActualRoundPush
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound ProcActualRoundTransition
theorem round_push (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (key : List Nat) (rd : Round) (s : Acc) (st' : PState) (t' : Nat)
    (hc : ProcActualReplayClock.Clock s) (hz : rd.key≠0 → rd.z=0)
    (hs : ProcActualAllowanceShape.Shape I.ids.length
      (ProcActualReplayEntry.state (entryAcc s) (ZkFormal.Chacha.rngAt key (position s))))
    (hv : ∀v∈rd.shuffled,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hsize : 1≤rd.bucket.length ∧ rd.bucket.length<16384)
    (htags : ProcActualBucketGuards.Tagged rd)
    (hb : ProcModelBatchTrace.Batch I.ids.length I.allowed (ProcActualConversionExact.view cv)
      (ProcActualReplayEntry.state (entryAcc s) (ZkFormal.Chacha.rngAt key (position s)))
      (cv.size+ProcActualEntryTransition.cursor (entryAcc s)) rd st' t') :
    ∃out,step I cv key rd s=.ok (.yield out) ∧ Aligned key cv out st' t' ∧
      ProcActualReplayClock.Clock out ∧
      (ProcActualGeneratedPush.pushes (entryAcc out)).toList=
        (ProcActualGeneratedPush.pushes (entryAcc s)).toList++
        (ProcPushEntries.pushes rd.key rd.z rd.steps).map (ProcPushConservation.stamp cv.size) := by
  have hcount := batch_count _ _ _ _ _ _ _ _ hb
  obtain ⟨last,next,hshuffle,hentry,hstate,hclock,hcursor,hentries,hrng,hpush⟩ :=
    ProcActualBatchPush.batch_push I cv hcv key (position s) (time s) (entryAcc s) rd st' t' hc hz hs hv hb
  rcases s with ⟨sb,rb,aa,gg,opsL,opsS,opsR,pushes,bucketsAll,T,kpos,Kq,zq,used,rounds,gidx⟩
  obtain ⟨collected,hcollect,_⟩ := ProcActualBucketGuards.collect_success cv.size rd.key rd.z rd.bucket bucketsAll htags
  dsimp only [position,time,entryAcc] at hshuffle hentry
  unfold step
  change ∃out : Acc,(do
    check (rd.bucket.length≥1 && rd.bucket.length<16384) "bucket size"
    let (sh,kend) ← replayShuffle key kpos (rd.bucket.map (fun b : Push=>b.v))
    check (sh==rd.shuffled) "shuffle replay differs"
    check (rd.steps.length==rd.bucket.length) "steps ≠ bucket"
    let collected ← forIn rd.bucket bucketsAll (ProcActualBucketGuards.collectStep cv.size rd.key rd.z)
    let result ← forIn (List.range rd.bucket.length)
      (sb,rb,aa,gg,opsL,opsS,opsR,pushes,used,gidx,#[])
      (ProcActualReplayEntry.step I cv rd sh T)
    pure (ForInStep.yield (result.1,result.2.1,result.2.2.1,result.2.2.2.1,
      result.2.2.2.2.1,result.2.2.2.2.2.1,result.2.2.2.2.2.2.1,result.2.2.2.2.2.2.2.1,
      collected,T+rd.bucket.length,kend,rd.key,rd.z,result.2.2.2.2.2.2.2.2.1,
      rounds.push ⟨rd.key,rd.z,T,rd.bucket.length,kpos,kend,Kq,zq,result.2.2.2.2.2.2.2.2.2.2.toList⟩,
      result.2.2.2.2.2.2.2.2.2.1)))=.ok (.yield out) ∧ Aligned key cv out st' t' ∧ ProcActualReplayClock.Clock out ∧
    (ProcActualGeneratedPush.pushes (entryAcc out)).toList=pushes.toList++
      (ProcPushEntries.pushes rd.key rd.z rd.steps).map (ProcPushConservation.stamp cv.size)
  simp only [hshuffle,hcount,hcollect,hentry,check,hsize.1,hsize.2,decide_true,
    Bool.and_true,BEq.rfl,ite_true,bind,Except.bind,pure,Except.pure]
  refine ⟨_,rfl,⟨hstate,hclock.symm⟩,?_,?_⟩
  · change T+rd.bucket.length=T0+ProcActualEntryTransition.cursor next
    rw [hcursor]
    change T=T0+gidx at hc
    dsimp only [entryAcc,ProcActualEntryTransition.cursor]
    omega
  · exact hpush

end ZkFormal.NearV3.Candidates.ProcActualRoundPush
