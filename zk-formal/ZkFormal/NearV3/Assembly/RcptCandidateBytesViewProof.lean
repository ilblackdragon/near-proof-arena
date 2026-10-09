import ZkFormal.NearV3.Assembly.RcptCandidateIndexedBytes
-- Source BytesViewProof.lean SHA256: feeb6e1621c4398e5ca434b6d3f009e2d922e5802177df88df6e37ca4c8b5fc8.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.IndexedBytes

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- There are no physical BYTES receive interactions in the receipt table. -/
theorem bytes_receive_empty :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BYTES false)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q _
  rw [rowT]
  simp [B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND]

theorem view_bytes_receive_empty (ls : RcptV3Vs) : rcptRecvs3 ls B_BYTES=[] := by
  simp [rcptRecvs3,rRecvs,B_BYTES,B_DIGEST,B_FINAL,B_MEM,B_SREC,B_AKC,B_BND]

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Complete actual BYTES sends match the unchanged final receipt-view API. -/
theorem ListChain.bytes_view {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    ((List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BYTES true)).Perm
      ((rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_BYTES).map Msg.toFp) := by
  have hh := ListChain.bytes_full hL h
  rw [chainByteMsgs_eq_view] at hh
  exact hh

/-- Both BYTES directions of `TableTraffic` hold for the concrete extracted list view. -/
theorem ListChain.bytes_view_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (m : List Fp) :
    tableBusCount RcptV3.interactions tr tt pub B_BYTES true m=
      ((rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_BYTES).map Msg.toFp).count m ∧
    tableBusCount RcptV3.interactions tr tt pub B_BYTES false m=
      ((rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_BYTES).map Msg.toFp).count m := by
  constructor
  · rw [tableBusCount_eq]
    exact (ListChain.bytes_view hL h).count_eq m
  · rw [tableBusCount_eq,bytes_receive_empty,view_bytes_receive_empty]
    rfl

/-- Every locally valid physical receipt table admits its concrete complete BYTES view. -/
theorem extract_bytes_view : ∃ bs : List ListBlock, ∃ e,
    ListChain tr tt 0 bs e ∧ ∀ m : List Fp,
    tableBusCount RcptV3.interactions tr tt pub B_BYTES true m=
      ((rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_BYTES).map Msg.toFp).count m ∧
    tableBusCount RcptV3.interactions tr tt pub B_BYTES false m=
      ((rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_BYTES).map Msg.toFp).count m := by
  obtain ⟨bs,e,hc⟩ := extract_lists hL
  exact ⟨bs,e,hc,ListChain.bytes_view_traffic hL hc⟩

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
