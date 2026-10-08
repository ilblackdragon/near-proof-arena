import ZkFormal.NearV3.Rcpt.Candidates.NativeNodeCanonical

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra Render.UpsGen

theorem node_occurrence_byte_sum (ts : List PTrie) :
    ((ts.flatMap occs).map (fun o => (nodeEnc o).length)).sum≤Assembly.preBytes ts := by
  induction ts with
  | nil => simp [Assembly.preBytes]
  | cons t ts ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,Assembly.preBytes,
      List.map_cons,List.sum_cons]
    have ht : ((occs t).map (fun o => (nodeEnc o).length)).sum≤unfoldedBytesT t := by
      simp only [unfoldedBytesT,Assembly.native_occs_eq]
      exact Nat.le_add_right _ _
    simp only [Assembly.preBytes] at ih
    omega

theorem native_forest_node_byte_bound (ts : List PTrie)
    (hb : Assembly.preBytes ts≤2000000) (o : PTrie) (ho : o∈ts.flatMap occs) :
    (nodeEnc o).length<ZkFormal.Algebra.P := by
  have hm:=Link3.le_sum_mem (List.mem_map.mpr ⟨o,ho,rfl⟩ :
    (nodeEnc o).length∈(ts.flatMap occs).map (fun o => (nodeEnc o).length))
  have hs:=node_occurrence_byte_sum ts
  change (nodeEnc o).length<2013265921
  omega

theorem native_forest_value_byte_bound (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (hb : Assembly.preBytes ts≤2000000) (b : Bytes) (h : b∈Assembly.forestBytes ts) :
    b.length<ZkFormal.Algebra.P := by
  have hsum := Link3.le_sum_mem (List.mem_map.mpr ⟨b,h,rfl⟩ :
    b.length∈(Assembly.forestBytes ts).map List.length)
  have hp := forest_occurrence_bytes ts hw
  simp only [Assembly.forestStoreViews,seedValues_bytes_length] at hp
  change b.length<2013265921
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
