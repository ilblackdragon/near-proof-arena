import ZkFormal.NearV3.Candidates.NativeQueryFinalTraffic
namespace ZkFormal.NearV3.Candidates.NativeQueryKey
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates.NodePostUpdate

theorem walk_key (w : WalkR) (syms : List Nat)
    (h:w.steps.map WStep3.sym=SYM_START::syms) :
    walkRecvs3 [w] B_KEYNIB=RcptE.keyMsgs w.w syms := by
  have hl:=congrArg List.length h
  simp only [List.length_map,List.length_cons] at hl
  simp only [walkRecvs3,show B_KEYNIB≠B_EDGE by decide,show B_KEYNIB≠B_BMAP by decide,
    ite_false,ite_true,List.flatMap_cons,List.flatMap_nil,List.append_nil,RcptE.keyMsgs,hl,Nat.add_sub_cancel]
  apply List.map_congr_left
  intro i hi
  have hi:=List.mem_range.mp hi
  have hiw:i+1<w.steps.length:=by omega
  have he:=congrArg (fun xs=>xs[i+1]?) h
  simp only [List.getElem?_map,List.getElem?_eq_getElem hiw,Option.map_some,List.getElem?_cons_succ] at he
  have hs:(w.step (i+1)).sym=syms.getD i 0:=by
    simp only [WalkR.step,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hiw,Option.getD_some,←he]
  rw [hs]
  congr 1
  congr 1
  congr 1
  have heq:(i+2=syms.length+1)↔(i+1=syms.length):=by omega
  simp only [heq]

theorem query_key (pairs : List (PTrie×PTrie)) (q : NativeLookupQuery) (w : WalkR)
    (h:nativeQueryWalk pairs q=some w) :
    walkRecvs3 [w] B_KEYNIB=RcptE.keyMsgs q.wid (q.key++[SYM_END]) := by
  cases hp:pairs[q.tau]? with
  | none=>simp [nativeQueryWalk,hp] at h
  | some pair=>
    obtain ⟨tree,post⟩:=pair
    cases hs:nativeLookupSteps (forestLookupNid ((pairs.take q.tau).map Prod.fst))
      (forestLookupVid ((pairs.take q.tau).map Prod.fst)) tree q.key with
    | none=>simp only [nativeQueryWalk,hp,bind,Option.bind,hs] at h;cases h
    | some ss=>
      simp only [nativeQueryWalk,hp,bind,Option.bind,hs] at h
      change some (nativeLookupWalk q.wid q.tau (forestLookupNid ((pairs.take q.tau).map Prod.fst)) tree ss)=some w at h
      cases h
      exact walk_key _ _ (nativeLookupWalk_symbols q.wid q.tau _ _ tree q.key ss hs)
end ZkFormal.NearV3.Candidates.NativeQueryKey
