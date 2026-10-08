import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemAggregate
import ZkFormal.NearV3.Rcpt.Candidates.ReceiptJobOrder
import ZkFormal.NearV3.Assembly.RcptCanonicalNativeViews
import ZkFormal.NearV3.Assembly.RcptCandidateMemoryWrites
import ZkFormal.NearV3.Assembly.RcptCandidateMemoryReads
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof Render
open Rcpt.Candidates

private theorem located_pairs (tr : Trace Fp) (lists : List (List Input)) :
    (locatedViews tr lists).zipIdx=
      (receiptLocations 0 (entityPlans lists)).map (fun x=>(rcptOf tr 0 (inputShape x.1 x.2.input),x.2.receiptIndex)) := by
  have hl:=congrArg List.length (native_locations_indices lists)
  simp only [List.length_map,List.length_range] at hl
  rw [List.zipIdx_eq_zip_range']
  apply Eq.symm
  apply List.zip_of_prod
  · simp only [List.map_map,locatedViews,Function.comp_def]
  · simp only [List.map_map,Function.comp_def]
    rw [native_locations_indices]
    simp only [locatedViews,List.length_map,hl,←List.range_eq_range']

/-- The unchanged list traffic API uses precisely the ordered physical
receipt slots; this equality does not discard duplicate receipts. -/
theorem located_mem_view (tr : Trace Fp) (lists : List (List Input))
    (pub : List Fp) (ls : RcptV3Vs) (h:flatR ls=locatedViews tr lists) :
    rcptSends3 pub ls B_MEM=locatedMemSends pub tr lists ∧
    rcptRecvs3 ls B_MEM=locatedMemRecvs tr lists := by
  constructor
  · have hh:=located_global_order ls 0 (fun r x=>rSends pub [] 0 r 0 x B_MEM)
    simp only [Nat.zero_add] at hh
    rw [h,located_pairs,List.flatMap_map] at hh
    change _=locatedMemSends pub tr lists at hh
    rw [←hh]
    unfold rcptSends3
    simp only [show B_MEM≠B_BYTES by decide,show B_MEM≠B_RCL by decide,if_false,List.nil_append]
    apply ZkFormal.Near.Render.flatMap_congr'
    intro j _
    apply ZkFormal.Near.Render.flatMap_congr'
    intro z _
    simp [rSends,B_MEM,B_BYTES,B_KEYNIB]
  · rw [ReceiptCandidateProof.memoryReadMsgs_view,h]
    simp only [locatedViews,List.flatMap_map,locatedMemRecvs]
    apply ZkFormal.Near.Render.flatMap_congr'
    intro x _
    simp [ReceiptCandidateProof.memoryReadMsgs,rRecvs,B_MEM,B_DIGEST,B_FINAL]

/-- Exact physical MEM counts on the same candidate-local receipt trace. -/
theorem physical_located_mem (tr : Trace Fp) (lists : List (List Input)) (pub : List Fp)
    (hL:TableLocal receiptArithmeticCandidate tr 0 pub) (bs : List ListBlock) (e : Nat)
    (hc:ListChain tr 0 0 bs e)
    (hf:flatR (bs.map (ListBlock.view tr 0))=locatedViews tr lists) (msg : List Fp) :
    tableBusCount RcptV3.interactions tr 0 pub B_MEM true msg=
      ((locatedMemSends pub tr lists).map Msg.toFp).count msg ∧
    tableBusCount RcptV3.interactions tr 0 pub B_MEM false msg=
      ((locatedMemRecvs tr lists).map Msg.toFp).count msg := by
  have hh:=located_mem_view tr lists pub _ hf
  constructor
  · rw [tableBusCount_eq,ReceiptCandidateProof.ListChain.memory_writes_view hL hc,hh.1]
  · rw [tableBusCount_eq,ReceiptCandidateProof.ListChain.memory_reads_view hL hc,hh.2]
end ZkFormal.NearV3.Assembly.RcptSkeleton
