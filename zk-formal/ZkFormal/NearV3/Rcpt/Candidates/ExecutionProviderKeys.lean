import ZkFormal.NearV3.Rcpt.Candidates.NativeExecutionJointCoverage

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen Assembly
open ZkFormal.NearV3.Candidates

theorem initialize_provider_nodes (ss : List NodeS3) (n : Nat) :
    (initializeList n ss).map (fun s=>providerNode s.v)=ss.map (fun s=>providerNode s.v) := by
  induction ss generalizing n with
  | nil=>rfl
  | cons s ss ih=>simp only [initializeList,List.map_cons,initializeMetadata,ih]

theorem chain_provider_nodes (cs : List StoreDuplicateChain.Entry) (ss : List NodeS3) (n : Nat) :
    (ChainMetadata.assign cs n ss).map (fun s=>providerNode s.v)=ss.map (fun s=>providerNode s.v) := by
  induction ss generalizing n with
  | nil=>rfl
  | cons s ss ih=>simp only [ChainMetadata.assign,List.map_cons,ChainMetadata.patch,ih]

/-- The actual initialized, duplicate-linked and post-updated provider retains
all original query/UPS keys. Usage counts can therefore be assigned afterwards. -/
theorem execution_provider_keys (u : Inputs) (cs : List StoreDuplicateChain.Entry) (ss : List NodeS3) :
    let provider:=records u (ChainMetadata.assign cs 0 (initializeList 0 ss))
    nodeEdgeKeys provider=nodeEdgeKeys ss ∧ nodeBitmapKeys provider=nodeBitmapKeys ss := by
  dsimp only
  rw [records_edge_keys,records_bitmap_keys]
  apply provider_keys_equal
  rw [chain_provider_nodes,initialize_provider_nodes]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
