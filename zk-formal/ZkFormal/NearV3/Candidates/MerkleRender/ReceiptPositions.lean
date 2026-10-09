import ZkFormal.NearV3.Candidates.MerkleRender.Isolation
import ZkFormal.NearV3.Rcpt.Candidates.ReceiptJobOrder

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Near.Render ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Rcpt.Candidates

private theorem flat_single {α β : Type} (xs : List α) (f : α→β) :
    xs.flatMap (fun x => [f x])=xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Receipt MPOS traffic is indexed in actual flattened execution order. -/
theorem receipt_position_order (pub : List Fp) (ls : RcptV3Vs) :
    rcptSends3 pub ls B_MPOS=(flatR ls).zipIdx.map (fun p => [0,p.2,msgId K_LEAF p.2,68]) := by
  have h := located_global_order ls 0 (fun r _ => [[0,r,msgId K_LEAF r,68]])
  simpa [rcptSends3,rSends,B_MPOS,B_BYTES,B_RCL,B_KEYNIB,B_MEM,B_RIDS,flat_single] using h

/-- Actual receipt leaf encodings supply precisely the Merkle leaf positions. -/
theorem receipt_leaf_positions (pub : List Fp) (ls : RcptV3Vs)
    (hl : ∀x∈flatR ls,x.leaf.length=68) :
    rcptSends3 pub ls B_MPOS=leafPositions ((flatR ls).map (fun x => x.leaf)) := by
  rw [receipt_position_order,leaf_positions,List.zipIdx_map,List.map_map]
  apply List.map_congr_left
  intro p hp
  have hm := List.fst_mem_of_mem_zipIdx hp
  change [0,p.2,msgId K_LEAF p.2,68]=[0,p.2,msgId K_LEAF p.2,p.1.leaf.length]
  rw [hl p.1 hm]

/-- Once receipt leaves are the native outcome preimages, the semantic receipt
traffic closes the physical Merkle MPOS bus exactly, with no cardinality premise. -/
theorem receipt_outcome_positions (pub : List Fp) (ls : RcptV3Vs) (os : List NearSpec.Outcome)
    (hn : os.length≤4481) (hl : ∀x∈flatR ls,x.leaf.length=68)
    (ho : (flatR ls).map (fun x => x.leaf)=outcomePreimages os) (m : List Fp) :
    ((rcptSends3 pub ls B_MPOS).map Msg.toFp).count m+
      tableBusCount MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub B_MPOS true m=
      tableBusCount MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub B_MPOS false m := by
  rw [receipt_leaf_positions pub ls hl,ho]
  exact outcome_positions os pub hn m

/-- Receipt validity discharges the fixed leaf length; only the native outcome
correspondence remains at this component boundary. -/
theorem receipt_wf_outcome_positions (pub : List Fp) (ls : RcptV3Vs) (os : List NearSpec.Outcome)
    (hn : os.length≤4481) (hw : ∀x∈flatR ls,∃r bg tok tok',x.Wf r bg tok tok')
    (ho : (flatR ls).map (fun x => x.leaf)=outcomePreimages os) (m : List Fp) :
    ((rcptSends3 pub ls B_MPOS).map Msg.toFp).count m+
      tableBusCount MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub B_MPOS true m=
      tableBusCount MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub B_MPOS false m := by
  apply receipt_outcome_positions pub ls os hn _ ho m
  intro x hx
  obtain ⟨r,bg,tok,tok',h⟩ := hw x hx
  exact (receipt_sha_lengths pub x h).2.2.1

end ZkFormal.NearV3.Candidates.MerkleRender
