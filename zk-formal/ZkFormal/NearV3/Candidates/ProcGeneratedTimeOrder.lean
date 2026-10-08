import ZkFormal.NearV3.Candidates.ProcPushSortContract
import ZkFormal.NearV3.Candidates.ProcPendingTime
namespace ZkFormal.NearV3.Candidates.ProcGeneratedTimeOrder
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def selectedTime (e : Step) : Option Nat := if e.ok && !e.last then some e.t else none

theorem entries_times (K z : Nat) (es : List Step) :
    (ProcPushEntries.pushes K z es).map Push.ts=es.filterMap selectedTime := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [ProcPushEntries.pushes,List.flatMap_cons,List.map_append,List.filterMap_cons] at ih ⊢
    unfold ProcPushEntries.pushOf selectedTime at ih ⊢
    split <;> simp_all

theorem generated_times (rs : List Round) :
    (ProcPushConservation.generated rs).map Push.ts=(rs.flatMap Round.steps).filterMap selectedTime := by
  simp only [ProcPushConservation.generated,List.map_flatMap,List.filterMap_flatMap,entries_times]

theorem selected_order (R : Nat) (es : List Step) (hs : ProcModelEntryShape.Stamped R es) :
    (es.filterMap selectedTime).Pairwise (·<·) ∧ ∀t∈es.filterMap selectedTime,R≤t := by
  have ho : es.Pairwise (fun a b=>a.t<b.t) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    rw [hs i hi,hs j hj]
    omega
  constructor
  · apply List.pairwise_filterMap.mpr
    apply ho.imp
    intro a b hab x hx y hy
    unfold selectedTime at hx hy
    split at hx <;> simp_all
  · intro t ht
    obtain ⟨e,he,hv⟩ := List.mem_filterMap.mp ht
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem he
    unfold selectedTime at hv
    split at hv
    · cases hv
      rw [hs i hi]
      omega
    · contradiction

theorem process_order (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    (ProcPushConservation.generated rs).Pairwise (fun a b=>a.ts<b.ts) ∧
      ∀p∈ProcPushConservation.generated rs,reqs.length≤p.ts := by
  have hh := selected_order reqs.length (rs.flatMap Round.steps)
    (ProcModelClock.process_clock n allowed reqs st0 st fuel rs h).1
  rw [←generated_times] at hh
  exact ⟨List.pairwise_map.mp hh.1,fun p hp=>hh.2 p.ts (List.mem_map_of_mem hp)⟩
theorem all_order (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    ((ProcModelStep.initial reqs st0).1++ProcPushConservation.generated rs).Pairwise
      (fun a b=>a.ts<b.ts) := by
  have hi := ProcPendingTime.initial reqs st0
  have hg := process_order n allowed reqs st0 st fuel rs h
  apply List.pairwise_append.mpr
  refine ⟨hi.1,hg.1,?_⟩
  intro a ha b hb
  have := hi.2 a ha
  have := hg.2 b hb
  omega

open NearSpecV3.Scheduler in
theorem replay_order (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∃out,ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok out ∧
      (ProcActualGeneratedPush.pushes (ProcActualReplayRound.entryAcc out)).toList.Pairwise
        (fun a b=>a.1<b.1) ∧
      (ProcActualGeneratedPush.pushes (ProcActualReplayRound.entryAcc out)).toList.Perm
        (ProcActualPoppedLog.buckets out).toList := by
  let I := ProcPreparedSequence.input sp prev
  obtain ⟨out,last,hr,ha,hclock,hpush,hpop⟩ := ProcActualTracePush.replay_push sp hs prev cv st rs hcv hproc
  have hreq : convRaw I.p I.ids.length I.raw=ProcActualConversionExact.view cv := by
    simpa [ProcActualConversionExact.view] using
      (ProcActualConversionExact.loop_view I I.raw #[] cv hcv).symm
  have hlen : (convRaw I.p I.ids.length I.raw).length=cv.size := by
    rw [hreq]; simp [ProcActualConversionExact.view]
  have hc : cv.size≤I.raw.length := by
    rw [←hlen]; exact List.length_filterMap_le _ _
  have hb := (ProcPreparedSequence.input_bounds sp prev hs).2.2
  have hconst : 4096≤T0 := by decide
  have hR : cv.size≤T0 := by change I.raw.length≤4096 at hb; omega
  have ho := ProcPushSortContract.stamped_order cv.size hR _
    (all_order I.ids.length I.allowed _ _ st _ rs hproc)
  rw [List.map_append,ProcActualInitialPush.initial_stamped I cv hcv] at ho
  have hp := ProcActualPoppedLog.process_conservation I cv st rs hproc out hr
  rw [List.map_append,ProcActualInitialPush.initial_stamped I cv hcv] at hp
  exact ⟨out,hr,by rw [hpush]; exact ho,by rw [hpush]; exact hp⟩

end ZkFormal.NearV3.Candidates.ProcGeneratedTimeOrder
