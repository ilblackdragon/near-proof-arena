import ZkFormal.NearV3.Candidates.NativeExecutionPost

namespace ZkFormal.NearV3.Candidates.PostMetadataPayloads
open ZkFormal.Near Rcpt.Candidates.NodePostUpdate

theorem initialize_map {α : Type} (f : NodeV3→α) (ss : List NodeS3) (n : Nat) :
    (initializeList n ss).map (fun s=>f s.v)=ss.map (fun s=>f s.v) := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp only [initializeList,List.map_cons,initializeMetadata,ih]

theorem chain_map {α : Type} (f : NodeV3→α) (cs : List StoreDuplicateChain.Entry)
    (ss : List NodeS3) (n : Nat) :
    (ChainMetadata.assign cs n ss).map (fun s=>f s.v)=ss.map (fun s=>f s.v) := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp only [ChainMetadata.assign,List.map_cons,ChainMetadata.patch,ih]

theorem uses_map {α : Type} (f : NodeV3→α) (q : UseRequests) (ss : List NodeS3) (n : Nat) :
    (assignList q n ss).map (fun s=>f s.v)=ss.map (fun s=>f s.v) := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp only [assignList,List.map_cons,assignUses,ih]

/-- The full metadata pipeline preserves the concrete post serialization list,
with counters computed after post updates. -/
theorem post_bytes (u : Inputs) (q : UseRequests) (cs : List StoreDuplicateChain.Entry)
    (ss : List NodeS3) :
    (assignList q 0 (records u (ChainMetadata.assign cs 0 (initializeList 0 ss)))).map
      (fun s=>s.v.ser true)=(records u ss).map (fun s=>s.v.ser true) := by
  rw [uses_map]
  simp only [records,List.map_map,Function.comp_def,record]
  rw [chain_map (fun v=>(node u v).ser true),initialize_map (fun v=>(node u v).ser true)]

end ZkFormal.NearV3.Candidates.PostMetadataPayloads
