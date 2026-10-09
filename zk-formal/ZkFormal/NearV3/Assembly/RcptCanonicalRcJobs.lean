import ZkFormal.NearV3.Assembly.RcptCanonicalRcPayloads
import ZkFormal.NearV3.Rcpt.Candidates.ReceiptShaPayloads

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof Rcpt.Candidates

theorem canonical_rc_sha_payloads (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hown : ∀i,i<8→pub.getD (PH_OWN+i) 0=Fp.ofNat (((u64 own).getD i 0).toNat))
    (hL : TableLocal ReceiptCandidateRouting.candidateTable (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 0 bs e) :

    rcShaPayloads pub (bs.map (RcptV3Proof.ListBlock.view (RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0))=
      lists.map (fun xs=>(u64 own++encodeReceipts (xs.map Input.receipt)).map UInt8.toNat) := by
  simpa [rcShaPayloads,List.map_map,Function.comp_def] using canonical_rc_payloads own ctx lists log constants pub digests fallback headerFallback hw hh hown hL bs e hc

theorem canonical_rc_sha_bytes (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hown : ∀i,i<8→pub.getD (PH_OWN+i) 0=Fp.ofNat (((u64 own).getD i 0).toNat))
    (hL : TableLocal ReceiptCandidateRouting.candidateTable (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 0 bs e) :

    ∀bytes∈rcShaPayloads pub (bs.map (RcptV3Proof.ListBlock.view (RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0)),∀b∈bytes,b<256 := by
  rw [canonical_rc_sha_payloads own ctx lists log constants pub digests fallback headerFallback hw hh hown hL bs e hc]
  intro bytes hb b hx
  obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hb
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
  exact UInt8.toNat_lt v

theorem canonical_rc_sha_digests (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hown : ∀i,i<8→pub.getD (PH_OWN+i) 0=Fp.ofNat (((u64 own).getD i 0).toNat))
    (hL : TableLocal ReceiptCandidateRouting.candidateTable (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 0 bs e) :

    (rcShaPayloads pub (bs.map (RcptV3Proof.ListBlock.view (RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0))).map (fun bytes=>(sha256 (bytes.map UInt8.ofNat)).map UInt8.toNat)=
      lists.map (fun xs=>(sha256 (u64 own++encodeReceipts (xs.map Input.receipt))).map UInt8.toNat) := by
  rw [canonical_rc_sha_payloads own ctx lists log constants pub digests fallback headerFallback hw hh hown hL bs e hc,List.map_map]
  apply List.map_congr_left
  intro xs hxs
  simp [Function.comp_def,List.map_map]

end ZkFormal.NearV3.Assembly.RcptSkeleton
