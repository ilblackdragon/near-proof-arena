import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderWindow
import ZkFormal.NearV3.Render.Node.HeaderBounds

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen Assembly

/-- Receipt replay preserves the accepted unfolded byte budget exactly. -/
theorem replay_preBytes (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid) :
    preBytes (rs.map ReplayTree.pre)=preBytes (rs.map ReplayTree.post) := by
  unfold preBytes
  congr 1
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro r hr
  exact (SizedAccountRun.unfolded_bytes (hv r hr)).symm

/-- The concrete initialized, updated providers retain node well-formedness
from the unchanged native byte cap. -/
theorem replay_provider_wf (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (hb : preBytes (rs.map ReplayTree.post)≤2000000)
    (u : Inputs) {i : Nat} {s : NodeS3}
    (hs : (records u (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre))))[i]?=some s) : s.v.wf := by
  have hmem:=List.mem_of_getElem? hs
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hmem
  obtain ⟨j,hj,o,ho,rfl⟩:=initializeList_member _ 0 a ha
  apply node_wf
  change o.v.wf
  obtain ⟨t,ht,tau,d,n,v,he,hn,hv'⟩:=forest_allocation _ 0 0 0 o (List.mem_of_getElem? ho)
  rw [he]
  apply native_forest_node_wf _ ?_ ?_ n v t ht
  · intro pre hp
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
    exact hw r hr
  · rw [replay_preBytes rs hv]
    exact hb

/-- The source message length agrees with the provider's pre-byte span, even
though copied bytes use its updated poststate serialization. -/
theorem replay_provider_span (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (hb : preBytes (rs.map ReplayTree.post)≤2000000)
    (u : Inputs) {i : Nat} {s : NodeS3}
    (hs : (records u (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre))))[i]?=some s) :
    (s.v.ser false).length=(s.v.ser true).length := by
  have hs:=replay_provider_wf rs hv hw hb u hs
  rw [NodeGen3.ser_len hs false,NodeGen3.ser_len hs true]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
