import ZkFormal.NearV3.Rcpt.Candidates.NodeEdgeDistinct
import ZkFormal.NearV3.Render.Ups.SchedulerExactInstances

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen UpsRows Assembly

def headEdgeKey (h : HeadE) : Msg := [0,h.tau,SYM_START,h.rres,0,EK_DOWN]
def headEdgeKeys (hs : List HeadE) : List Msg := hs.map headEdgeKey

def nodeBitmapKeys (ss : List NodeS3) : List Msg :=
  (ss.zip (List.range ss.length)).filterMap (fun (s,n)=>s.v.bmap.map (fun (bm,hv)=>[n,bm,hv]))

theorem nodeBitmapKeys_of_get {ss : List NodeS3} {n bm hv : Nat} {s : NodeS3}
    (h : ss[n]?=some s) (hb : s.v.bmap=some (bm,hv)) : [n,bm,hv]∈nodeBitmapKeys ss := by
  have hn : n<ss.length := (List.getElem?_eq_some_iff.mp h).1
  have hs : ss[n]=s := (List.getElem?_eq_some_iff.mp h).2
  apply List.mem_filterMap.mpr
  refine ⟨(s,n),?_,by simp [hb]⟩
  apply List.mem_of_getElem? (i:=n)
  simp [hn,hs]

theorem nodeBitmapKeys_distinct (ss : List NodeS3) : (nodeBitmapKeys ss).Nodup := by
  have hz:=Near.Render.BusEdge.zip_range_pairwise ss 0
  rw [←List.range_eq_range'] at hz
  refine (List.Pairwise.filterMap (S:=fun a b=>a.getD 0 0<b.getD 0 0) _ ?_ hz).imp
    (fun h e=>by rw [e] at h;omega)
  intro a a' haa b hb b' hb'
  cases hh : a.1.v.bmap with
  | none=>simp [hh] at hb
  | some x=>
    cases hh' : a'.1.v.bmap with
    | none=>simp [hh'] at hb'
    | some y=>
      cases x;cases y
      simp [hh] at hb
      simp [hh'] at hb'
      subst b b'
      simpa using haa

theorem exact_native_start_coverage (pairs : List (PTrie×PTrie)) (run : TreeRun) (I : Render.UpsInst)
    (h : ExactNativeWalkProviders pairs run I) :
    (step I 0).e∈headEdgeKeys (forestWalkHeads 0 0 pairs) := by
  obtain ⟨_,_,hd,_,hh,hs,_⟩:=h
  have he : (step I 0).e=headEdgeKey hd := by
    change (step I 0).e++[0]=headEdgeKey hd++[0] at hs
    exact List.append_cancel_right hs
  exact List.mem_map.mpr ⟨hd,List.mem_of_getElem? hh,he.symm⟩

theorem exact_native_terminal_coverage (pairs : List (PTrie×PTrie)) (run : TreeRun) (I : Render.UpsInst)
    (h : ExactNativeWalkProviders pairs run I) :
    [((step I I.ts).e).getD 0 0,(step I I.ts).bm,(step I I.ts).hv]∈
      nodeBitmapKeys (forestStoreViews (pairs.map Prod.fst)).nodes ∨
    (step I I.ts).e∈nodeEdgeKeys (forestStoreViews (pairs.map Prod.fst)).nodes := by
  obtain ⟨a,s,_,hs,_,_,_,hid,ht⟩:=h
  rcases ht with ⟨_,hb⟩|he
  · left;rw [hid];exact nodeBitmapKeys_of_get hs hb
  · right;exact nodeEdgeKeys_of_get hs he

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
