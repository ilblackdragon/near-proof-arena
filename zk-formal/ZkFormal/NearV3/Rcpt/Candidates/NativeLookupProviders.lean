import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountLookup
import ZkFormal.NearV3.Rcpt.Candidates.UpsRequestCoverage

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

/-- EDGE providers in the actual occurrence order, starting at the allocated ID. -/
def indexedNodeEdges : Nat→List NodeS3→List Msg
  | _,[]=>[]
  | n,s::ss=>edgesOf3 n s++indexedNodeEdges (n+1) ss

theorem indexedNodeEdges_append (n : Nat) (a b : List NodeS3) :
    indexedNodeEdges n (a++b)=indexedNodeEdges n a++indexedNodeEdges (n+a.length) b := by
  induction a generalizing n with
  | nil=>simp [indexedNodeEdges]
  | cons s a ih=>simp [indexedNodeEdges,ih,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem indexedNodeEdges_zip (n : Nat) (ss : List NodeS3) :
    indexedNodeEdges n ss=(ss.zip (List.range' n ss.length)).flatMap (fun (s,i)=>edgesOf3 i s) := by
  induction ss generalizing n with
  | nil=>rfl
  | cons s ss ih=>simp [indexedNodeEdges,List.range'_succ,ih]

theorem indexedNodeEdges_zero (ss : List NodeS3) : indexedNodeEdges 0 ss=nodeEdgeKeys ss := by
  rw [indexedNodeEdges_zip]
  simp only [nodeEdgeKeys,List.range_eq_range']

theorem lookupDrain_no_edges (key : List Nat) (s : WStep3) (h : s∈lookupDrain key) : ¬s.mode≤1 := by
  obtain ⟨a,_,rfl⟩:=List.mem_map.mp h
  simp

/-- The next stored-key symbol is supplied by its actual key edge. -/
theorem keyEdges3_at_prefix (nid : Nat) (pre rest : List Nat) (a : Nat) :
    [nid,pre.length,a,nid,pre.length+1,EK_KEY]∈keyEdges3 nid (pre++a::rest) := by
  apply List.mem_map.mpr
  refine ⟨pre.length,List.mem_range.mpr (by simp),?_⟩
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_right]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
