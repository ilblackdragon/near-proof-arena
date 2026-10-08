import ZkFormal.NearV3.Rcpt.Candidates.NodePostFacts
import ZkFormal.NearV3.Rcpt.Candidates.NativeProviderCoverage

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near

/-- Post digest replacement never changes the branch membership provider. -/
theorem record_bitmap (u : Inputs) (s : NodeS3) : (record u s).v.bmap=s.v.bmap := by
  cases hv:s.v with
  | leaf k v m=>simp [record,node,NodeV3.bmap,hv]
  | ext k c m=>simp [record,node,NodeV3.bmap,hv]
  | branch v cs m=>cases v <;> simp [record,node,NodeV3.bmap,hv,bitmap]

/-- Exact ordered EDGE providers retain the original occurrence IDs even when
all child and value post digests have been updated. -/
theorem records_edge_keys (u : Inputs) (ss : List NodeS3) :
    nodeEdgeKeys (records u ss)=nodeEdgeKeys ss := by
  simp only [nodeEdgeKeys,records,List.length_map,List.zip_map_left,List.flatMap_map]
  congr 1
  funext p
  exact record_edges u p.2 p.1

theorem records_bitmap_keys (u : Inputs) (ss : List NodeS3) :
    nodeBitmapKeys (records u ss)=nodeBitmapKeys ss := by
  simp only [nodeBitmapKeys,records,List.length_map,List.zip_map_left,List.filterMap_map]
  congr 1
  funext p
  simp only [Prod.map,Function.comp_apply,id_eq,record_bitmap]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
