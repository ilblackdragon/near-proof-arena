import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayDigestPartition
import ZkFormal.NearV3.Candidates.NodeUseLocal
import ZkFormal.NearV3.Candidates.ChainMetadata

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

theorem initialize_node_views (ss : List NodeS3) (n : Nat) :
    (initializeList n ss).map NodeS3.v=ss.map NodeS3.v := by
  induction ss generalizing n with
  | nil=>rfl
  | cons s ss ih=>simp only [initializeList,List.map_cons,initializeMetadata,ih]

theorem chain_node_views (cs : List Candidates.StoreDuplicateChain.Entry) (ss : List NodeS3) (n : Nat) :
    (Candidates.ChainMetadata.assign cs n ss).map NodeS3.v=ss.map NodeS3.v := by
  induction ss generalizing n with
  | nil=>rfl
  | cons s ss ih=>simp only [Candidates.ChainMetadata.assign,List.map_cons,Candidates.ChainMetadata.patch,ih]

theorem usage_node_views (q : UseRequests) (ss : List NodeS3) (n : Nat) :
    (assignList q n ss).map NodeS3.v=ss.map NodeS3.v := by
  induction ss generalizing n with
  | nil=>rfl
  | cons s ss ih=>simp only [assignList,List.map_cons,assignUses,ih]

theorem records_node_views (u : Inputs) {as bs : List NodeS3}
    (h : as.map NodeS3.v=bs.map NodeS3.v) :
    (records u as).map NodeS3.v=(records u bs).map NodeS3.v := by
  simpa only [records,List.map_map,Function.comp_def,record] using congrArg (List.map (node u)) h

/-- Counter/duplicate metadata updates preserve every child digest request;
post-byte mutation stays before window-use assignment in the actual pipeline. -/
theorem pipeline_child_digests (u : Inputs) (q : UseRequests)
    (cs : List Candidates.StoreDuplicateChain.Entry) (ss : List NodeS3) :
    (assignList q 0 (records u (Candidates.ChainMetadata.assign cs 0 (initializeList 0 ss)))).flatMap childDigests=
      (records u ss).flatMap childDigests := by
  have hh:=(usage_node_views q _ 0).trans
    (records_node_views u ((chain_node_views cs _ 0).trans (initialize_node_views ss 0)))
  let f:=fun v : NodeV3=>v.revealed.flatMap fun (c,l,_,pre,post)=>
    [digMsg (msgId K_NPRE c) l pre,digMsg (msgId K_NPOST c) l post]
  have he:=congrArg (List.flatMap f) hh
  simp only [List.flatMap_map] at he
  exact he

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
