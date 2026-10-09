import ZkFormal.NearV3.Candidates.ProcConversionExact
import ZkFormal.NearV3.Candidates.ProcGrantAgreement
namespace ZkFormal.NearV3.Candidates.ProcConvertedLinks
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def Links (n : Nat) (cv : Array CReq) : Prop := ∀c∈cv.toList,c.link=c.s*n+c.r

theorem step_links (I : Input) (q : RawReq) (cv : Array CReq) (hs : Links I.ids.length cv)
    (out : ForInStep (Array CReq)) (h : ProcConverted.step I q cv=.ok out) :
    ExceptLoop.StepInv (Links I.ids.length) out := by
  unfold ProcConverted.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | intro c hc
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hc
      rcases hc with hc|rfl
      · exact hs c hc
      · rfl

theorem loop_links (I : Input) (out : Array CReq)
    (h : forIn I.raw #[] (ProcConverted.step I)=.ok out) : Links I.ids.length out :=
  ExceptLoop.invariant I.raw (ProcConverted.step I) (Links I.ids.length)
    (fun q _ cv hs out h=>step_links I q cv hs out h) #[] out (by simp [Links]) h

theorem view_get (cv : Array CReq) (i : Nat) (hi : i<cv.size) :
    (ProcConversionExact.view cv).toArray[i]! =
      ({link:=cv[i]!.link,incs:=cv[i]!.incs} : NearSpecV3.Scheduler.Req) := by
  have hv : i<(ProcConversionExact.view cv).toArray.size := by
    simpa [ProcConversionExact.view] using hi
  rw [getElem!_pos (ProcConversionExact.view cv).toArray i hv,getElem!_pos cv i hi]
  simp [ProcConversionExact.view]

theorem indexed_link (I : Input) (cv : Array CReq)
    (h : forIn I.raw #[] (ProcConverted.step I)=.ok cv) (i : Nat) (hi : i<cv.size) :
    cv[i]!.link=cv[i]!.s*I.ids.length+cv[i]!.r := by
  apply loop_links I cv h
  rw [getElem!_pos cv i hi]
  exact List.mem_iff_getElem.mpr ⟨i,hi,Array.getElem_toList hi⟩

/-- Actual conversion chooses the same source and receiver coordinates as the
model request; grant agreement therefore applies at every valid selected ID. -/
theorem selected_grant (I : Input) (cv : Array CReq)
    (h : forIn I.raw #[] (ProcConverted.step I)=.ok cv)
    (i inc : Nat) (hi : i<cv.size) (st : PState) :
    ProcGrantAgreement.modelGrant I.ids.length I.allowed
      (ProcConversionExact.view cv).toArray[i]!.link inc st =
    ProcGrantAgreement.replayGrant I.allowed cv[i]!.s cv[i]!.r cv[i]!.link inc st := by
  rw [view_get cv i hi]
  apply ProcGrantAgreement.grant_eq
  · have hf := ProcConvertedFacts.loop_facts I cv h
    have hm : cv[i]!∈cv.toList := by
      rw [getElem!_pos cv i hi]
      exact List.mem_iff_getElem.mpr ⟨i,hi,Array.getElem_toList hi⟩
    exact (hf _ hm).2.1
  · exact indexed_link I cv h i hi
end ZkFormal.NearV3.Candidates.ProcConvertedLinks
