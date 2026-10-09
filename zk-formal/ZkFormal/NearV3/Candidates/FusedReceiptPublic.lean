import ZkFormal.NearV3.Candidates.FusedReceiptMemory
import ZkFormal.NearV3.Assembly.RcptCandidateFamilyPublicMemory
import ZkFormal.NearV3.Assembly.RcptCandidatePublicAdmission
namespace ZkFormal.NearV3.Candidates.FusedReceiptPublic
open ZkFormal.V2 NearSpecV3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near HorizontalTrace
open Assembly.ReceiptCandidateRouting RcptV3Proof

/-- Actual global AIR balance and sender inventory discharge receipt memory
ownership. The receipt semantics and traffic come from the same fused views.
This proves the receipt component, not full NEAR transition soundness. -/
theorem extract {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (hA : AP.toAir=GatedMemoryAdmission.air) (hs : AP.pubSegs=Public.preparedSegments)
    (h : HoldsP AP pub tr)
    (hp : Assembly.ReceiptCandidateProof.ReceiptPublicRanges pub) :
    ∃off,∃bs : List ListBlock,∃e,
      ListChain (project off tr) 0 0 bs e ∧
      RcptV3Wf pub (bs.map (ListBlock.view (project off tr) 0)) ∧
      TableTraffic candidateTable.interactions (project off tr) 0 pub
        (rcptTraffic3 pub (bs.map (ListBlock.view (project off tr) 0))) := by
  exact FusedReceiptMemory.extract_sound (Assembly.ReceiptFamilyMemory.holdsP_fused_local hA h)
    hp (Assembly.ReceiptFamilyMemory.holdsP_fused_receive_version hA hs h)
/-- Prepared public bytes and their actual admission discharge public receipt
ranges. No external MEM ownership, version or public body-range premise remains.
This still establishes the receipt component only, not complete NEAR soundness. -/
theorem prepared {AP : AirP} {tr : Trace Fp}
    (hA : AP.toAir=GatedMemoryAdmission.air) (hs : AP.pubSegs=Public.preparedSegments)
    (hmax : AP.maxPub+8<ZkFormal.Algebra.P)
    {cb : NearSpec.Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint=.ok p)
    (overhead : Nat)
    (h : HoldsP AP (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) tr) :
    let pub:=ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)
    ∃off,∃bs : List ListBlock,∃e,
      ListChain (project off tr) 0 0 bs e ∧
      RcptV3Wf pub (bs.map (ListBlock.view (project off tr) 0)) ∧
      TableTraffic candidateTable.interactions (project off tr) 0 pub
        (rcptTraffic3 pub (bs.map (ListBlock.view (project off tr) 0))) := by
  exact extract hA hs h (Assembly.ReceiptPublicAdmission.prepared_ranges hs hmax hp overhead h.pubFit)

/-- The same component result for the admitted bounded-routing representation. -/
theorem bounded_prepared {AP : AirP} {tr : Trace Fp}
    (hA : AP.toAir=GatedMemoryAdmission.air) (hs : AP.pubSegs=Public.preparedSegments)
    (hmax : AP.maxPub+8<ZkFormal.Algebra.P)
    {cb : NearSpec.Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint=.ok p)
    (l : Layout) (own overhead : Nat)
    (h : HoldsP AP (ZkFormal.Udr.pubOf Fp (Public.preparedBytes (Assembly.RoutingBoundedLayout.boundedPrep p l own) overhead)) tr) :
    let pub:=ZkFormal.Udr.pubOf Fp (Public.preparedBytes (Assembly.RoutingBoundedLayout.boundedPrep p l own) overhead)
    ∃off,∃bs : List ListBlock,∃e,
      ListChain (project off tr) 0 0 bs e ∧
      RcptV3Wf pub (bs.map (ListBlock.view (project off tr) 0)) ∧
      TableTraffic candidateTable.interactions (project off tr) 0 pub
        (rcptTraffic3 pub (bs.map (ListBlock.view (project off tr) 0))) := by
  exact extract hA hs h (Assembly.ReceiptPublicAdmission.bounded_prepared_ranges hs hmax hp l own overhead h.pubFit)

end ZkFormal.NearV3.Candidates.FusedReceiptPublic
