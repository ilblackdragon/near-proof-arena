import ZkFormal.NearV3.Candidates.ReceiptDigestPartition
import ZkFormal.NearV3.Candidates.MerkleRender.ReceiptPositions
namespace ZkFormal.NearV3.Candidates.ReceiptNativeMerklePositions
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3Proof

theorem extracted_leaf_lengths (tr : Trace Fp) (t : Nat) (bs : List ListBlock) :
    ∀x∈flatR (bs.map (ListBlock.view tr t)),x.leaf.length=68 := by
  intro x hx
  obtain ⟨L,hL,hx⟩:=List.mem_flatMap.mp hx
  obtain ⟨B,hB,rfl⟩:=List.mem_map.mp hL
  change x∈B.receipts.map (rcptOf tr t) at hx
  obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
  simp [RcptV.leaf,rcptOf,colAt]

theorem physical (tr : Trace Fp) (t : Nat) (pub : List Fp) (bs : List ListBlock)
    (os : List NearSpec.Outcome) (hn : os.length≤4481)
    (hl : (flatR (bs.map (ListBlock.view tr t))).map (fun x=>x.leaf)=MerkleRender.outcomePreimages os)
    (ht : TableTraffic Assembly.ReceiptCandidateRouting.candidateTable.interactions tr t pub
      (rcptTraffic3 pub (bs.map (ListBlock.view tr t)))) (msg : List Fp) :
    tableBusCount Assembly.ReceiptCandidateRouting.candidateTable.interactions tr t pub B_MPOS true msg+
      tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace os pub) T_MRK pub B_MPOS true msg=
      tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace os pub) T_MRK pub B_MPOS false msg := by
  rw [(ht B_MPOS msg).1]
  exact MerkleRender.receipt_outcome_positions pub _ os hn (extracted_leaf_lengths tr t bs) hl msg

end ZkFormal.NearV3.Candidates.ReceiptNativeMerklePositions
