import ZkFormal.NearV3.Assembly.RcptSourceRcOutputs
import ZkFormal.NearV3.Assembly.RcptCanonicalRcJobs

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates RcptV3Proof

private theorem map_getD_range {α β : Type} (xs : List α) (d : α) (f : α→β) :
    (List.range xs.length).map (fun j=>f (xs.getD j d))=xs.map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    rw [←List.getElem_eq_getD (h:=by simpa using hi) d]

/-- Exact native input list SHA bytes match every occurrence job in the gated
source RC inventory; hash output suppression never changes this list. -/
theorem source_rc_job_preimages (own : Nat) (ctx : ApplyCtx)
    (sources : List SrcList) (entries : List ProofEntry) :
    (sourceRcShaJobs own sources entries).map (·.bytes)=
      (sourceInputLists ctx sources entries).map (fun xs=>
        (u64 own++encodeReceipts (xs.map Input.receipt)).map UInt8.toNat) := by
  simp only [sourceRcShaJobs,List.map_map,Function.comp_def,DedupCompile.entryAt]
  change (List.range sources.length).map (fun j=>(u64 own++encodeReceipts
    (sourceEntry entries (sources.getD j ⟨[],0,[]⟩)).receipts).map UInt8.toNat)=_
  rw [map_getD_range sources ⟨[],0,[]⟩ (fun s=>(u64 own++encodeReceipts (sourceEntry entries s).receipts).map UInt8.toNat)]
  simp [sourceInputLists,nativeInputs,nativeInput,List.map_map,Function.comp_def,sourceEntry]

theorem canonical_source_rc_jobs (own : Nat) (ctx : ApplyCtx) (sources : List SrcList) (entries : List ProofEntry)
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈(sourceInputLists ctx sources entries),∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hown : ∀i,i<8→pub.getD (PH_OWN+i) 0=Fp.ofNat (((u64 own).getD i 0).toNat))
    (hL : TableLocal ReceiptCandidateRouting.candidateTable (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx (sourceInputLists ctx sources entries) log constants pub digests fallback headerFallback) 0) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx (sourceInputLists ctx sources entries) log constants pub digests fallback headerFallback) 0) 0 0 bs e) :

    rcShaPayloads pub (bs.map (RcptV3Proof.ListBlock.view (RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx (sourceInputLists ctx sources entries) log constants pub digests fallback headerFallback) 0) 0))=
      (sourceRcShaJobs own sources entries).map (·.bytes) := by
  rw [source_rc_job_preimages own ctx sources entries]
  exact canonical_rc_sha_payloads own ctx (sourceInputLists ctx sources entries) log constants pub digests fallback headerFallback hw hh hown hL bs e hc

end ZkFormal.NearV3.Assembly.RcptSkeleton
