import ZkFormal.NearV3.Candidates.NativeReceiptQueryGate
import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemTraffic
import ZkFormal.NearV3.Assembly.RcptCandidateKeyTraffic
namespace ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly RcptSkeleton RcptV3 RcptV3Proof Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

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

theorem located_key_view (tr : Trace Fp) (lists : List (List Input))
    (pub : List Fp) (ls : RcptV3Vs) (h:flatR ls=locatedViews tr lists) :
    rcptSends3 pub ls B_KEYNIB=(receiptLocations 0 (entityPlans lists)).flatMap
      (fun x=>rSends pub [] 0 x.2.receiptIndex 0 (rcptOf tr 0 (inputShape x.1 x.2.input)) B_KEYNIB) := by
  have hh:=located_global_order ls 0 (fun r x=>rSends pub [] 0 r 0 x B_KEYNIB)
  simp only [Nat.zero_add] at hh
  rw [h,located_pairs,List.flatMap_map] at hh
  rw [←hh]
  unfold rcptSends3
  simp only [show B_KEYNIB≠B_BYTES by decide,show B_KEYNIB≠B_RCL by decide,ite_false,List.nil_append]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro j _
  apply ZkFormal.Near.Render.flatMap_congr'
  intro z _
  simp [rSends,B_KEYNIB,B_BYTES]

theorem physical_keys (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw:∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh:2^log<Algebra.P) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId constants) pub digests fallback headerFallback) 0
    ∀(hL:TableLocal receiptArithmeticCandidate tr 0 pub) (bs : List ListBlock) (e : Nat),
      ListChain tr 0 0 bs e→∀msg,
      tableBusCount RcptV3.interactions tr 0 pub B_KEYNIB true msg=
        (((accountLookupQueries (lists.flatten.map Input.receipt)++
          accessKeyLookupQueries (lists.flatten.map Input.receipt)).flatMap
          (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END]))).map Msg.toFp).count msg := by
  intro tr hL bs e hc msg
  have hf:=canonical_native_views own ctx lists log _ pub digests fallback headerFallback hw hh hL bs e hc
  have hv:=located_key_view tr lists pub (bs.map (ListBlock.view tr 0)) hf
  have hm:(rcptSends3 pub (bs.map (ListBlock.view tr 0)) B_KEYNIB).Perm
      ((accountLookupQueries (lists.flatten.map Input.receipt)++accessKeyLookupQueries (lists.flatten.map Input.receipt)).flatMap
        (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END]))) := by
    rw [hv]
    have he:(receiptLocations 0 (entityPlans lists)).flatMap
        (fun x=>rSends pub [] 0 x.2.receiptIndex 0 (rcptOf tr 0 (inputShape x.1 x.2.input)) B_KEYNIB)=
        (receiptLocations 0 (entityPlans lists)).flatMap
        (fun x=>(receiptQueries x.2.input.receipt x.2.receiptIndex).flatMap
          (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END]))) := by
      apply ZkFormal.Near.Render.flatMap_congr'
      intro x hx
      obtain ⟨before,after,hb,hoff⟩:=native_locations_block lists x.1 x.2 hx
      have hi:x.2.input∈lists.flatten := by
        have hm:x.2.input∈(receiptLocations 0 (entityPlans lists)).map (fun y=>y.2.input):=List.mem_map.mpr ⟨x,hx,rfl⟩
        rw [receiptLocations_inputs,entityPlans_inputs] at hm
        exact hm
      obtain ⟨xs,hxs,hix⟩:=List.mem_flatten.mp hi
      rw [hoff]
      exact physical_key_inventory own ctx k lists log constants pub digests accountId fallback headerFallback x.2 before after hb (hw xs hxs x.2.input hix) [] 0 0
    rw [he]
    simpa only [List.flatMap_assoc] using List.Perm.flatMap_right
      (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END])) (located lists)
  have ht:=ReceiptCandidateProof.ListChain.key_view_traffic hL hc msg
  exact ht.1.trans ((hm.map Msg.toFp).count_eq msg)
end ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
