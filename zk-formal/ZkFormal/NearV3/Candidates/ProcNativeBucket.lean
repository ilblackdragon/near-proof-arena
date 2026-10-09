import ZkFormal.NearV3.Candidates.ProcNativeState
import ZkFormal.NearV3.Candidates.ProcConvertedPointers
namespace ZkFormal.NearV3.Candidates.ProcNativeBucket
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcRequestPointers ProcNativeGrant

theorem reqAt_source (reqs : List Req) (v : Nat) (hv : Valid reqs v) :
    reqAt reqs v=⟨reqs.toArray[v/64]!.link,reqs.toArray[v/64]!.incs.drop (v%64)⟩ := by
  unfold reqAt
  have hi : v/64<reqs.toArray.size := by simpa using hv.1
  rw [getElem!_pos reqs.toArray (v/64) hi]
  simp [List.getD_eq_getElem?_getD,hv.1]

theorem step_state (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z t v : Nat) (st : St) (hv : Valid reqs v) :
    (stepE n allowed reqs K z t v st).1=
      (tryGrant n allowed st reqs.toArray[v/64]!.link
        (reqs.toArray[v/64]!.incs.getD (v%64) 0)).2 := by
  unfold stepE
  rw [reqAt_source reqs v hv]
  simp only [List.drop_eq_getElem_cons hv.2]
  split <;> simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hv.2,Option.getD_some]

theorem runL_state (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (hv : ∀v∈vs,Valid reqs v) (t : Nat) (st : St) :
    (runL n allowed reqs K z vs t st).1=ProcNativeState.replay n allowed reqs vs st := by
  induction vs generalizing t st with
  | nil => rfl
  | cons v vs ih =>
    simp only [runL]
    rw [ih (fun w hw=>hv w (by simp [hw]))]
    rw [step_state n allowed reqs K z t v st (hv v (by simp))]
    rfl

/-- The actual native bucket processor reaches precisely the event model's
post-state. Its request tails come from valid encoded pointers, and its grant
arithmetic is the checked saturating native implementation. -/
theorem entries_bucket_state (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool)
    (reqs : List Req) (hR : ∀q∈reqs,q.incs.length<64)
    (K z : Nat) (vs : List Nat) (hv : ∀v∈vs,Valid reqs v)
    (s out : ProcModelStep.EntryAcc) (hs : Inv n M s.2.1)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) (P : List PM) :
    (processBucket n allowed (vs.map (reqAt reqs)) (native s.2.1,bucketsOf reqs P)).1=
      native out.2.1 := by
  rw [processBucket_runL n allowed reqs hR K z vs s.2.2.1 (native s.2.1) P]
  rw [runL_state n allowed reqs K z vs hv]
  exact (ProcNativeState.entries_native n M hM allowed reqs K z vs s out hs h).symm
end ZkFormal.NearV3.Candidates.ProcNativeBucket
