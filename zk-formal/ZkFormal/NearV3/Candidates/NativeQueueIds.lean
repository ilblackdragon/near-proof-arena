import ZkFormal.NearV3.Candidates.NativeReceiptAccessIds
import ZkFormal.NearV3.Rcpt.Candidates.NativeQueueLookup

namespace ZkFormal.NearV3.Candidates.NativeQueueIds
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates.NodePostUpdate
open Qv Qv.Candidates.CombinedWalkGen

def resolve (pre : PTrie) (v : MainValues) (pres : List PTrie) : Resolve := fun tau slot=>
  let input:=(queueInputs pre v pres).getD tau (.hash [],[])
  let request:=input.2.getD slot ⟨[],none,.raw⟩
  ((valueIndex input.1 request.key).map (fun i=>
    ((forestBytes ((pre::pres).take tau)).length+i,queueUsers input.1 (input.2.take slot) i))).getD (0,0)

/-- Provider identities do not change the actual requested trie paths. -/
theorem queries_independent (pre : PTrie) (v : MainValues) (pres : List PTrie) (a b : Resolve) :
    queueLookupQueries pre v pres a=queueLookupQueries pre v pres b := by
  simp [queueLookupQueries,plan,mainPlan,implicitPlan,mainWalk,queueLookupQuery,
    Walk.request,List.map_append,List.map_map,Function.comp_def]

theorem query_result (pairs : List (PTrie×PTrie)) (q : NativeLookupQuery)
    (tree post : PTrie) (w : WalkR) (hp:pairs[q.tau]?=some (tree,post))
    (hw:nativeQueryWalk pairs q=some w) :
    w.steps.getLast?.map lookupFinal=some
      ((valueIndex tree q.key).map ((forestBytes ((pairs.take q.tau).map Prod.fst)).length+·)) := by
  simp only [nativeQueryWalk,hp,bind,Option.bind] at hw
  cases hs:nativeLookupSteps (forestLookupNid ((pairs.take q.tau).map Prod.fst))
      (forestLookupVid ((pairs.take q.tau).map Prod.fst)) tree q.key with
  | none=>simp only [hs,reduceCtorEq] at hw
  | some ss=>
    simp only [hs] at hw
    change some (nativeLookupWalk q.wid q.tau (forestLookupNid ((pairs.take q.tau).map Prod.fst)) tree ss)=some w at hw
    have he:=Option.some.inj hw
    subst w
    exact nativeLookupWalk_valueIndex q.wid q.tau _ _ tree q.key ss hs

/-- The queue renderer uses the exact original forest offset and local VID
of its actual request, with the number of preceding uses of that VID. -/
theorem resolve_at (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (w : Walk)
    (tree : PTrie) (requests : List ReadRequest)
    (ht:(queueInputs pre v pres)[w.tau]?=some (tree,requests))
    (hr:requests[w.slot]?=some (w.request v.shards)) :
    resolve pre v pres w.tau w.slot=
      ((valueIndex tree (w.request v.shards).key).map (fun i=>
        ((forestBytes ((pre::pres).take w.tau)).length+i,queueUsers tree (requests.take w.slot) i))).getD (0,0) := by
  simp [resolve,List.getD_eq_getElem?_getD,ht,hr]

theorem plan_resolved (pre : PTrie) (v : MainValues) (pres : List PTrie) (f : Resolve)
    (w : Walk) (hw:w∈plan pre v pres f) : (w.vid,w.users)=f w.tau w.slot := by
  rcases List.mem_append.mp hw with hm|hi
  · simp only [mainPlan,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with (rfl|rfl|rfl)|hm
    · rfl
    · rfl
    · rfl
    · obtain ⟨⟨shard,i⟩,_,rfl⟩:=List.mem_map.mp hm
      rfl
  · obtain ⟨⟨tree,i⟩,_,rfl⟩:=List.mem_map.mp hi
    rfl

theorem find_presence (tree : PTrie) (key : List Nat) (value : Option Bytes)
    (hf:tree.find key=some value) : (valueIndex tree key).isSome=value.isSome := by
  cases value with
  | none=>
    cases hi:valueIndex tree key with
    | none=>rfl
    | some i=>
      obtain ⟨bytes,hb⟩:=valueIndex_defined tree key i hi
      rw [hf] at hb
      cases Option.some.inj hb
  | some bytes=>
    obtain ⟨i,hi,_⟩:=valueIndex_complete tree key bytes hf
    simp only [hi,Option.isSome_some]

/-- Every actual planned queue query uses its original forest VID and correct
presence flag, including implicit prestates whose ordinal allocation differs. -/
theorem plan_value (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (w : Walk) (hw:w∈plan pre v pres (resolve pre v pres))
    (hholds:∀x∈queueInputs pre v pres,∀r∈x.2,r.Holds x.1) :
    ∃tree requests,(queueInputs pre v pres)[w.tau]?=some (tree,requests) ∧
      requests[w.slot]?=some (w.request v.shards) ∧
      ((valueIndex tree (w.request v.shards).key).map
        ((forestBytes ((pre::pres).take w.tau)).length+·))=
        (if w.value.isSome then some w.vid else none) := by
  obtain ⟨tree,requests,ht,hr,_⟩:=plan_slot hw
  have hres:=(plan_resolved pre v pres (resolve pre v pres) w hw).trans
    (resolve_at pre v pres w tree requests ht hr)
  have hvid:=congrArg Prod.fst hres
  have hfind:tree.find (w.request v.shards).key=some w.value:=
    (hholds (tree,requests) (List.mem_of_getElem? ht) _ (List.mem_of_getElem? hr)).1
  have hpres:=find_presence tree (w.request v.shards).key w.value hfind
  refine ⟨tree,requests,ht,hr,?_⟩
  rw [←hpres]
  cases hi:valueIndex tree (w.request v.shards).key with
  | none=>rfl
  | some i=>
    simp only [hi,Option.map_some,Option.getD_some] at hvid
    simp only [Option.map_some,Option.isSome_some,ite_true]
    exact congrArg some hvid.symm

theorem plan_rank (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (w : Walk) (hw:w∈plan pre v pres (resolve pre v pres))
    (tree : PTrie) (requests : List ReadRequest)
    (ht:(queueInputs pre v pres)[w.tau]?=some (tree,requests))
    (hr:requests[w.slot]?=some (w.request v.shards)) (i : Nat)
    (hi:valueIndex tree (w.request v.shards).key=some i) :
    w.users=queueUsers tree (requests.take w.slot) i := by
  have h:=(plan_resolved pre v pres (resolve pre v pres) w hw).trans
    (resolve_at pre v pres w tree requests ht hr)
  have hs:=congrArg Prod.snd h
  simpa only [hi,Option.map_some,Option.getD_some] using hs

end ZkFormal.NearV3.Candidates.NativeQueueIds
