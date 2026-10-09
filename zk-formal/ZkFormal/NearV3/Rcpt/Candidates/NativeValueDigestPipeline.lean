import ZkFormal.NearV3.Rcpt.Candidates.NativeValueDigestForest
import ZkFormal.NearV3.Rcpt.Candidates.EmptyValueComplete
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

theorem pipeline_preSlot (u : Inputs) (q : UseRequests)
    (cs : List Candidates.StoreDuplicateChain.Entry) (ss : List NodeS3) :
    (assignList q 0 (records u (Candidates.ChainMetadata.assign cs 0 (initializeList 0 ss)))).flatMap preSlotDigests=
      (records u ss).flatMap preSlotDigests := by
  have hh:=(usage_node_views q _ 0).trans
    (records_node_views u ((chain_node_views cs _ 0).trans (initialize_node_views ss 0)))
  let f:=fun v : NodeV3=>match v.value with
    | some (i,l,pre,_,_)=>[digMsg (msgId K_VPRE i) l pre]
    | none=>[]
  have he:=congrArg (List.flatMap f) hh
  simp only [List.flatMap_map] at he
  exact he

theorem metadata_value_digests (cs : List Candidates.StoreDuplicateChain.Entry) (es : List ValE) :
    EmptyValue.valueDigests (Candidates.ChainMetadata.assignValues cs es)=EmptyValue.valueDigests es := by
  simp [EmptyValue.valueDigests,Candidates.ChainMetadata.assignValues,List.map_map,
    Function.comp_def,Candidates.ChainMetadata.patchValue]

/-- Same actual initialized/duplicate-tagged/post-updated/provider-counted node
forest and duplicate-tagged value list, preserving every occurrence and ID. -/
theorem native_preSlot_inventory (u : Inputs) (q : UseRequests)
    (cs : List Candidates.StoreDuplicateChain.Entry) (ts : List PTrie) :
    (assignList q 0 (records u (Candidates.ChainMetadata.assign cs 0
      (initializeList 0 (forestNodes 0 0 0 ts))))).flatMap preSlotDigests=
      EmptyValue.valueDigests (Candidates.ChainMetadata.assignValues cs (seedValuesFrom 0 (forestBytes ts))) := by
  rw [pipeline_preSlot,updated_value_digests,metadata_value_digests]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
