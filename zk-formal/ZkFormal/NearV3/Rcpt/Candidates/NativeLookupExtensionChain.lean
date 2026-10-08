import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupChainTools

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near

theorem lookupExtensionEdges_chain (nid target : Nat) (key : List Nat) :
    lookupChain (lookupExtensionEdges nid target key) := by
  apply (lookupChain_indexed _).mpr
  intro i hi
  have hi' : i+1<key.length := by simpa [lookupExtensionEdges] using hi
  have hn : i+1≠key.length := by omega
  simp only [lookupExtensionEdges,List.getElem_map,List.getElem_range,lookupEdge,lookupNext]
  simp [hn]

theorem lookupExtensionEdges_last_target (nid target : Nat) (key : List Nat)
    (s : WStep3) (h : (lookupExtensionEdges nid target key).getLast?=some s) :
    s.mode=0 ∧ (s.e.drop 3).take 2=[target,0] := by
  have hn : 0<key.length := by
    by_cases hz : key=[]
    · subst key;simp [lookupExtensionEdges] at h
    · exact List.length_pos_iff.mpr hz
  rw [List.getLast?_eq_getElem?] at h
  simp only [lookupExtensionEdges,List.length_map,List.length_range,List.getElem?_map,List.getElem?_range] at h
  rw [List.getElem?_eq_getElem (by simp;omega),List.getElem_range] at h
  simp only [Option.map_some,Option.some.injEq] at h
  rw [←h]
  simp [lookupEdge,show key.length-1+1=key.length by omega]

theorem lookupExtensionEdges_first_source (nid target : Nat) (key : List Nat)
    (s : WStep3) (h : (lookupExtensionEdges nid target key).head?=some s) :
    s.mode=0 ∧ s.e.take 2=[nid,0] := by
  cases key with
  | nil=>simp [lookupExtensionEdges] at h
  | cons a as=>
    simp only [List.head?_eq_getElem?,lookupExtensionEdges,List.getElem?_map,List.getElem?_range,
      List.length_cons,show 0<as.length+1 by omega,ite_true,Option.map_some,Option.some.injEq] at h
    rw [←h]
    simp [lookupEdge]

theorem lookupExtensionEdges_append_chain (nid target : Nat) (key : List Nat)
    (tail : List WStep3) (ht : lookupChain tail)
    (hf : ∀s,tail.head?=some s→s.e.take 2=[target,0] ∧ s.mode≤2) :
    lookupChain (lookupExtensionEdges nid target key++tail) := by
  apply lookupChain_append _ tail (lookupExtensionEdges_chain nid target key) ht
  intro a b ha hb
  have hlast:=lookupExtensionEdges_last_target nid target key a ha
  have hfirst:=hf b hb
  exact lookupNext_matched a b hlast.1 (hfirst.1.trans hlast.2.symm) hfirst.2

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
