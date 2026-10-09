import ZkFormal.NearV3.Candidates.ProcActualReplayClock
namespace ZkFormal.NearV3.Candidates.ProcActualBatchPush
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.Chacha
open ProcActualReplayEntry ProcActualEntryTransition

/-- One retained model batch yields successful shuffle and actual entry replay,
with the exact next native state, clock, and RNG position. -/
theorem batch_push (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (key : List Nat) (k T : Nat) (s : Acc) (rd : Round) (st' : PState) (t' : Nat)
    (hT : T=T0+cursor s) (hz : rd.key≠0 → rd.z=0)
    (hs : ProcActualAllowanceShape.Shape I.ids.length (state s (rngAt key k)))
    (hv : ∀v∈rd.shuffled,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hb : ProcModelBatchTrace.Batch I.ids.length I.allowed (ProcActualConversionExact.view cv)
      (state s (rngAt key k)) (cv.size+cursor s) rd st' t') :
    ∃last out,replayShuffle key k (rd.bucket.map (·.v))=.ok (rd.shuffled,last) ∧
      forIn (List.range rd.bucket.length) s (step I cv rd rd.shuffled T)=.ok out ∧
      state out (rngAt key last)=st' ∧ t'=cv.size+cursor out ∧
      cursor out=cursor s+rd.bucket.length ∧
      (entries out).size=(entries s).size+rd.bucket.length ∧ st'.rng=rngAt key last ∧
      (ProcActualGeneratedPush.pushes out).toList=(ProcActualGeneratedPush.pushes s).toList++
        (ProcPushEntries.pushes rd.key rd.z rd.steps).map (ProcPushConservation.stamp cv.size) := by
  obtain ⟨rng,pending,modelOut,hshuffle,hmodel,hsteps,hstate,htime,hstart⟩ := hb
  obtain ⟨last,hr,hrng⟩ := ProcShuffleReplay.replay_of_shuffle key k _ _ _ hshuffle
  have hlen : rd.bucket.length=rd.shuffled.length := by
    simpa using (shuffle_perm hshuffle).length_eq.symm
  rw [hrng] at hmodel
  obtain ⟨out,ho,he,hcursor,hentries⟩ := model_batch_success I cv hcv rd rd.shuffled T s
    (rngAt key last) pending modelOut hv hs hmodel hsteps hlen
  have hc := (ProcModelEntryShape.entries_counts I.ids.length I.allowed
    (ProcActualConversionExact.view cv) rd.key rd.z rd.shuffled _ modelOut hmodel).1
  have hg := ProcModelRng.entries_rng I.ids.length I.allowed
    (ProcActualConversionExact.view cv) rd.key rd.z rd.shuffled _ modelOut hmodel
  have hp := ProcActualGeneratedPush.model_batch_push I cv hcv rd rd.shuffled T s out
    (rngAt key last) pending modelOut hv hs hmodel hsteps hlen hT hz ho
  refine ⟨last,out,hr,ho,he.trans hstate.symm,?_,hcursor,hentries,?_,hp⟩
  · rw [htime,hc,hcursor,hlen]
    simp only
    omega
  · rw [hstate,hg]
end ZkFormal.NearV3.Candidates.ProcActualBatchPush
