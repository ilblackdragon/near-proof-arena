import ZkFormal.NearV3.Rcpt.Candidates.WalkRequestInventory
import ZkFormal.NearV3.Render.Ups.SchedulerInstances

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen UpsRows Assembly

def nodeEdgeKeys (ss : List NodeS3) : List Msg :=
  (ss.zip (List.range ss.length)).flatMap (fun (s,n)=>edgesOf3 n s)

theorem nodeEdgeKeys_of_get {ss : List NodeS3} {n : Nat} {s : NodeS3} {e : Msg}
    (h : ss[n]?=some s) (he : e∈edgesOf3 n s) : e∈nodeEdgeKeys ss := by
  have hn : n<ss.length := (List.getElem?_eq_some_iff.mp h).1
  apply List.mem_flatMap.mpr
  refine ⟨(s,n),?_,he⟩
  apply List.mem_of_getElem? (i:=n)
  have hs : ss[n]=s := (List.getElem?_eq_some_iff.mp h).2
  simp [hn,hs]

/-- Proper-prefix requests only: START is supplied by heads and the terminal
row has a separate edge-or-bitmap proof in NativeWalkProviders. -/
def upsPrefixEdgeKeys (I : Render.UpsInst) : List Msg :=
  ((List.range I.ts).filter (fun t=>1≤t)).map (fun t=>(step I t).e)

theorem native_ups_prefix_coverage (pairs : List (PTrie×PTrie)) (run : TreeRun) (I : Render.UpsInst)
    (h : NativeWalkProviders pairs run I) :
    ∀e∈upsPrefixEdgeKeys I,e∈nodeEdgeKeys (forestStoreViews (pairs.map Prod.fst)).nodes := by
  obtain ⟨_,_,_,_,_,_,hp,_⟩:=h
  intro e he
  obtain ⟨t,ht,rfl⟩:=List.mem_map.mp he
  have ht':=List.mem_filter.mp ht
  obtain ⟨n,s,hs,he⟩:=hp t (by simpa using ht'.2) (List.mem_range.mp ht'.1)
  exact nodeEdgeKeys_of_get hs he

theorem assigned_node_edge_coverage (q : UseRequests) {ss : List NodeS3} {n : Nat} {s : NodeS3}
    {e : Msg} (h : ss[n]?=some s) (he : e∈edgesOf3 n s) : e∈nodeEdgeKeys (assignList q 0 ss) := by
  have hh : (assignList q 0 ss)[n]?=some (assignUses q n s) := by simp [assignList_get,h]
  exact nodeEdgeKeys_of_get hh he

theorem assigned_native_ups_prefix_coverage (q : UseRequests)
    (pairs : List (PTrie×PTrie)) (run : TreeRun) (I : Render.UpsInst)
    (h : NativeWalkProviders pairs run I) :
    ∀e∈upsPrefixEdgeKeys I,
      e∈nodeEdgeKeys (assignList q 0 (forestStoreViews (pairs.map Prod.fst)).nodes) := by
  obtain ⟨_,_,_,_,_,_,hp,_⟩:=h
  intro e he
  obtain ⟨t,ht,rfl⟩:=List.mem_map.mp he
  have ht':=List.mem_filter.mp ht
  obtain ⟨n,s,hs,he⟩:=hp t (by simpa using ht'.2) (List.mem_range.mp ht'.1)
  exact assigned_node_edge_coverage q hs he

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
