import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupMismatchShape

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

theorem extension_interior_provider (nid vid tau depth : Nat) (key : List Nat)
    (child : PTrie) (mem j : Nat) (hj : j+1<key.length) :
    [nid,j,key.getD j 0,nid,j+1,EK_KEY]∈
      edgesOf3 nid (seedNodeView tau depth nid vid (.ext key child mem)) := by
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨j,List.mem_range.mpr (by simp;omega),?_⟩
  simp [List.getD_eq_getElem?_getD,List.getElem?_dropLast,show j<key.length-1 by omega, List.getElem?_eq_getElem (show j<key.length by omega)]

theorem extension_last_provider (nid vid tau depth : Nat) (key : List Nat)
    (child : PTrie) (mem j : Nat) (hj : j+1=key.length) :
    [nid,j,key.getD j 0,if isNode child then viewTarget (nid+1) child else nid,
      if isNode child then 0 else key.length,EK_KEY]∈
      edgesOf3 nid (seedNodeView tau depth nid vid (.ext key child mem)) := by
  have hlt : j<key.length := by omega
  have hlast : key.getLast?=some (key.getD j 0) := by
    rw [List.getLast?_eq_getElem?,show key.length-1=j by omega]
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlt]
  apply List.mem_append_right
  simp only [seedNodeView,viewNode,viewKid]
  cases hn : isNode child <;> simp [hn,hlast,show key.length-1=j by omega]

theorem extension_mismatch_edge_coverage (nid vid tau depth : Nat) (stored : List Nat)
    (child : PTrie) (mem : Nat) (key : List Nat) (raw : List WStep3)
    (hp : isPrefix stored key=false) (h : leafLookupSteps nid vid (.ref 0 []) 0 stored key=some raw) :
    ∀s∈extensionMismatchFix nid child stored.length raw,s.mode≤1→s.e∈
      edgesOf3 nid (seedNodeView tau depth nid vid (.ext stored child mem)) := by
  intro s hs hm
  unfold extensionMismatchFix at hs
  split at hs
  · rename_i hc
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hs
    rw [extensionMismatchStep_mode] at hm
    obtain ⟨j,hj,he,hbefore⟩:=leaf_mismatch_shape nid vid (.ref 0 []) stored 0 key raw hp h r hr hm
    simp only [Nat.zero_add] at he
    by_cases hlast : j+1=stored.length
    · have hmode : r.mode=1 := by have hh:=hbefore;omega
      simp only [extensionMismatchStep,hmode,he,List.getD_cons_zero,List.getD_cons_succ,
        hlast,EK_KEY,ite_true,true_and,and_self]
      simpa [hc,EK_KEY] using extension_last_provider nid vid tau depth stored child mem j hlast
    · have hi : j+1<stored.length := by omega
      have hn : ¬(r.e.getD 1 0+1=stored.length) := by simpa [he] using hlast
      simp only [extensionMismatchStep,hn,and_false,false_and,ite_false]
      rw [he]
      exact extension_interior_provider nid vid tau depth stored child mem j hi
  · rename_i hc
    obtain ⟨j,hj,he,hbefore⟩:=leaf_mismatch_shape nid vid (.ref 0 []) stored 0 key raw hp h s hs hm
    simp only [Nat.zero_add] at he
    rw [he]
    by_cases hlast : j+1=stored.length
    · simpa [hc,hlast] using extension_last_provider nid vid tau depth stored child mem j hlast
    · exact extension_interior_provider nid vid tau depth stored child mem j (by omega)

theorem extension_matched_edge_coverage (nid vid tau depth : Nat) (stored : List Nat)
    (child : PTrie) (mem : Nat) (hc : isNode child=true) :
    ∀s∈lookupExtensionEdges nid (viewTarget (nid+1) child) stored,s.e∈
      edgesOf3 nid (seedNodeView tau depth nid vid (.ext stored child mem)) := by
  intro s hs
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hs
  have hj' := List.mem_range.mp hj
  by_cases hl : j+1=stored.length
  · simpa [lookupEdge,hl,hc] using extension_last_provider nid vid tau depth stored child mem j hl
  · simpa [lookupEdge,hl] using extension_interior_provider nid vid tau depth stored child mem j (by omega)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
