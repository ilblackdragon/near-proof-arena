import ZkFormal.NearV3.Candidates.NativeRankedAccountIds
namespace ZkFormal.NearV3.Candidates.NativeQueryFinal
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates.NodePostUpdate

def message (wid tau : Nat) (result : Option Nat) : Msg :=
  [wid,tau,if result.isSome then FK_VAL else FK_ABS,result.getD 0]

/-- Convert the exact last-step option into the actual FINAL bus tuple. This
retains proven absence as FK_ABS rather than discarding absent queries. -/
theorem walk_message (w : WalkR) (result : Option Nat)
    (h:w.steps.getLast?.map lookupFinal=some result) :
    [w.w,w.tau,w.fk,w.k]=message w.w w.tau result := by
  cases hs:w.steps.getLast? with
  | none=>simp [hs] at h
  | some s=>
    have hlast:w.last=s:=by
      unfold WalkR.last WalkR.step
      have hi:=List.getLast?_eq_getElem? (l:=w.steps)
      rw [hs] at hi
      simp only [List.getD_eq_getElem?_getD,←hi,Option.getD_some]
    simp only [hs,Option.map_some,Option.some.injEq] at h
    rw [←h]
    by_cases hz:s.mode=0 <;> simp [WalkR.fk,WalkR.k,hlast,lookupFinal,hz,message]

theorem ranked_message (previous : List WStep3) (w : WalkR) (result : Option Nat)
    (h:w.steps.getLast?.map lookupFinal=some result) :
    [(rankWalk previous w).w,(rankWalk previous w).tau,(rankWalk previous w).fk,(rankWalk previous w).k]=
      message w.w w.tau result := by
  exact walk_message (rankWalk previous w) result ((NativeRankedAccountIds.final_preserved previous w).trans h)

def result (pairs : List (PTrie×PTrie)) (q : NativeLookupQuery) : Option Nat :=
  ((pairs[q.tau]?).map (fun p=>(valueIndex p.1 q.key).map
    (forestLookupVid ((pairs.take q.tau).map Prod.fst)+·))).getD none

def queryMessage (pairs : List (PTrie×PTrie)) (q : NativeLookupQuery) : Msg :=
  message q.wid q.tau (result pairs q)

theorem query_message (pairs : List (PTrie×PTrie)) (q : NativeLookupQuery) (w : WalkR)
    (h:nativeQueryWalk pairs q=some w) :
    [w.w,w.tau,w.fk,w.k]=queryMessage pairs q := by
  cases hp:pairs[q.tau]? with
  | none=>simp [nativeQueryWalk,hp] at h
  | some pair=>
    obtain ⟨tree,post⟩:=pair
    cases hs:nativeLookupSteps (forestLookupNid ((pairs.take q.tau).map Prod.fst))
      (forestLookupVid ((pairs.take q.tau).map Prod.fst)) tree q.key with
    | none=>simp only [nativeQueryWalk,hp,bind,Option.bind,hs] at h;cases h
    | some ss=>
      simp only [nativeQueryWalk,hp,bind,Option.bind,hs,Option.some.injEq] at h
      change some (nativeLookupWalk q.wid q.tau (forestLookupNid ((pairs.take q.tau).map Prod.fst)) tree ss)=some w at h
      cases h
      have hv:=nativeLookupWalk_valueIndex q.wid q.tau _ _ tree q.key ss hs
      simpa only [queryMessage,result,hp,Option.map_some,Option.getD_some,nativeLookupWalk] using walk_message _ _ hv
end ZkFormal.NearV3.Candidates.NativeQueryFinal
