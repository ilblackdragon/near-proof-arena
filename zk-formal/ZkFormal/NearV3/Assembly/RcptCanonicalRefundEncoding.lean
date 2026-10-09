import ZkFormal.NearV3.Assembly.RcptRefundLedger
import ZkFormal.NearV3.Assembly.RcptCanonicalNativeViews
import ZkFormal.NearV3.Assembly.RcptNativeRefundEncoding

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

private theorem flatMap_congr {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,h x (by simp),ih (fun y hy=>h y (by simp [hy]))]

variable (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hflag : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)

private abbrev nativeTrace := RoutingQCandidate.patchTrace
  (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0

include hw hflag in
theorem located_refund_encodings :
    (locatedViews (nativeTrace own ctx k lists accountId accessId log constants pub digests fallback headerFallback) lists).flatMap
      (fun x=>if x.hr then [x.encRefund] else [])=
      (lists.flatten.map Input.receipt).flatMap (fun r=>(nativeRefunds ctx r).map (fun rr=>rr.encode.map UInt8.toNat)) := by
  have hi := receiptLocations_inputs (entityPlans lists) 0
  rw [entityPlans_inputs] at hi
  rw [←hi,List.map_map,List.flatMap_map]
  unfold locatedViews
  rw [List.flatMap_map]
  apply flatMap_congr
  intro a ha
  obtain ⟨pre,post,hb,ho⟩ := native_locations_block lists a.1 a.2 ha
  have hm : a.2.input∈lists.flatten := by rw [←hi];exact List.mem_map.mpr ⟨a,ha,rfl⟩
  obtain ⟨xs,hxs,hm⟩ := List.mem_flatten.mp hm
  have hf := hflag xs hxs a.2.input hm
  dsimp only [Function.comp_def]
  rw [ho]
  change (if a.2.input.refund then [_] else [])=_
  cases hr : a.2.input.refund
  · simp only [Bool.false_eq_true,ite_false,nativeRefunds,←hf,hr,List.map_nil]
  · simp only [ite_true,nativeRefunds,←hf,hr,List.map_cons,List.map_nil]
    congr 1
    exact native_refund_encoding own ctx k lists accountId accessId log constants pub digests fallback
      headerFallback a.2 pre post hb (hw xs hxs a.2.input hm) hf hr

include hw hflag in
theorem canonical_outgoing_encodings (t : PTrie) (out : MainOut)
    (hex : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hh : 2^log<Algebra.P)
    (hL : TableLocal ReceiptCandidateRouting.candidateTable
      (nativeTrace own ctx k lists accountId accessId log constants pub digests fallback headerFallback) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (nativeTrace own ctx k lists accountId accessId log constants pub digests fallback headerFallback) 0 0 bs e) :
    (flatR (bs.map (RcptV3Proof.ListBlock.view
      (nativeTrace own ctx k lists accountId accessId log constants pub digests fallback headerFallback) 0))).flatMap
      (fun x=>if x.hr then [x.encRefund] else [])=out.outgoing.map (fun rr=>rr.encode.map UInt8.toNat) := by
  rw [canonical_native_views own ctx lists log constants pub (nativeDigests ctx digests)
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback hw hh
    (ReceiptCandidateProof.repaired_local_base hL) bs e hc]
  rw [located_refund_encodings own ctx k lists accountId accessId log constants pub digests fallback headerFallback hw hflag,
    applyNewChunk_refund_ledger ctx t _ out hex,List.map_flatMap]

end ZkFormal.NearV3.Assembly.RcptSkeleton
