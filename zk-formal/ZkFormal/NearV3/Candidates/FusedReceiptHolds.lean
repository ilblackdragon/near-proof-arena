import ZkFormal.NearV3.Candidates.FusedReceiptMemory
import ZkFormal.NearV3.Assembly.RcptCandidateFamilyMemory
namespace ZkFormal.NearV3.Candidates.FusedReceiptHolds
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near HorizontalTrace
open Assembly.ReceiptCandidateRouting RcptV3Proof

/-- Actual global AIR balance and sender inventory discharge receipt memory
ownership. The receipt semantics and traffic come from the same fused views.
This proves the receipt component, not full NEAR transition soundness. -/
theorem extract {tr : Trace Fp} {pub : List Fp}
    (h : Holds GatedMemoryAdmission.air pub tr)
    (hp : Assembly.ReceiptCandidateProof.ReceiptPublicRanges pub) :
    ∃off,∃bs : List ListBlock,∃e,
      ListChain (project off tr) 0 0 bs e ∧
      RcptV3Wf pub (bs.map (ListBlock.view (project off tr) 0)) ∧
      TableTraffic candidateTable.interactions (project off tr) 0 pub
        (rcptTraffic3 pub (bs.map (ListBlock.view (project off tr) 0))) := by
  exact FusedReceiptMemory.extract_sound (Assembly.ReceiptFamilyMemory.fused_local h)
    hp (Assembly.ReceiptFamilyMemory.fused_receive_version h)
end ZkFormal.NearV3.Candidates.FusedReceiptHolds
