import ZkFormal.NearV3.Candidates.NativeNodeLocal
import ZkFormal.NearV3.Rcpt.Candidates.NodeUsageList
namespace ZkFormal.NearV3.Candidates.NodeUseLocal
open ZkFormal.Near ZkFormal.Algebra Render Rcpt.Candidates.NodePostUpdate

theorem getD (q : UseRequests) (vs : List NodeS3) (i : Nat) (hi : i<vs.length) :
    (assignList q 0 vs).getD i default=assignUses q i (vs.getD i default) := by
  have hh:=assignList_get q vs 0 i
  have ha : i<(assignList q 0 vs).length := by simpa [assignList_length] using hi
  simpa [List.getD,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem ha] using hh

theorem cid (q : UseRequests) (vs : List NodeS3) (i p : Nat) (hi : i<vs.length) :
    NodeGen3.cidAt (assignList q 0 vs) i p=NodeGen3.cidAt vs i p := by
  simp only [NodeGen3.cidAt,NodeGen3.layN,NodeGen3.rec,getD q vs i hi,assignUses]

/-- Assigning exact request multiplicities preserves all honest node-generator
requirements, including initialized child-ID arrays. -/
theorem node_ok (q : UseRequests) (vs : List NodeS3) (hn : NodeOk vs)
    (he : q.edges.length<Algebra.P) (hb : q.bmaps.length<Algebra.P) (hw : q.windows.length<Algebra.P) :
    NodeOk (assignList q 0 vs) := by
  refine ⟨assignList_wf q vs hn.wf he hb hw,?_,?_,?_,?_,?_⟩
  · simpa [assignList_length] using hn.pos
  · intro s hs
    obtain ⟨i,o,ho,rfl⟩:=assignList_member q vs 0 s hs
    exact hn.depth o ho
  · intro s hs
    obtain ⟨i,o,ho,rfl⟩:=assignList_member q vs 0 s hs
    exact hn.lenB o ho
  · simpa [assignList_bytes] using hn.rows
  · intro n hni p hp
    have hi : n<vs.length := by simpa [assignList_length] using hni
    rw [getD q vs n hi] at hp ⊢
    rw [cid q vs n p hi]
    exact hn.ucid n hi p hp

theorem complete (q : UseRequests) (vs : List NodeS3) (hn : NodeOk vs)
    (he : q.edges.length<Algebra.P) (hb : q.bmaps.length<Algebra.P) (hw : q.windows.length<Algebra.P)
    (t : Nat) (pub : List Fp) :
    TableLocal Rcpt.Candidates.SizeCount.nodeTable (TrieCountHeight.node (assignList q 0 vs) pub) t pub :=
  TrieCountHeight.node_local _ (node_ok q vs hn he hb hw) t pub
end ZkFormal.NearV3.Candidates.NodeUseLocal
