import ZkFormal.NearV3.Rcpt.Candidates.NodeEdgeDistinct
import ZkFormal.NearV3.Rcpt.Candidates.NodeUsage

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near

/-- One provider key per actual pre-serialization byte, retaining the global
node index and updated post byte. -/
def nodeWindowKeys (ss : List NodeS3) : List Msg :=
  (ss.zip (List.range ss.length)).flatMap fun (s,n)=>
    (List.range (s.v.ser false).length).map fun p=>windowKey n p s

theorem windowKey_injective (s : NodeS3) (n p q : Nat)
    (h : windowKey n p s=windowKey n q s) : p=q := by
  have hh:=congrArg (fun xs=>xs[1]?) h
  simpa [windowKey] using hh

theorem windowKey_index (s u : NodeS3) (n m p q : Nat)
    (h : windowKey n p s=windowKey m q u) : n=m := by
  have hh:=congrArg List.head? h
  simp only [windowKey,List.head?_cons,Option.some.injEq,msgId] at hh
  omega

theorem nodeWindowKeys_distinct (ss : List NodeS3) : (nodeWindowKeys ss).Nodup := by
  unfold nodeWindowKeys List.Nodup
  rw [List.pairwise_flatMap]
  constructor
  · intro x hx
    rw [List.pairwise_map]
    exact List.nodup_range.imp (fun {a b} hne he=>hne (windowKey_injective x.1 x.2 a b he))
  · have hz:=Near.Render.BusEdge.zip_range_pairwise ss 0
    rw [←List.range_eq_range'] at hz
    refine hz.imp_of_mem (fun {_ _} _ _ hlt a ha b hb he=>?_)
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp ha
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hb
    have hn:=windowKey_index _ _ _ _ p q he
    omega

theorem nodeWindowKeys_mem {ss : List NodeS3} {s : NodeS3} {n p : Nat}
    (hs : ss[n]?=some s) (hp : p<(s.v.ser false).length) :
    windowKey n p s∈nodeWindowKeys ss := by
  have hn : n<ss.length := List.getElem?_eq_some_iff.mp hs |>.1
  have hz : (s,n)∈ss.zip (List.range ss.length) := by
    apply List.mem_of_getElem? (i:=n)
    have hnz : n<(ss.zip (List.range ss.length)).length := by simp; exact hn
    rw [List.getElem?_eq_getElem hnz]
    simp only [List.getElem_zip,List.getElem_range,Option.some.injEq,Prod.mk.injEq]
    exact ⟨(List.getElem?_eq_some_iff.mp hs).2,True.intro⟩
  apply List.mem_flatMap.mpr
  exact ⟨(s,n),hz,List.mem_map.mpr ⟨p,List.mem_range.mpr hp,rfl⟩⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
