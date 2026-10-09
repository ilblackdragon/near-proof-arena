import ZkFormal.NearV3.Candidates.NativeReceiptFinalView
import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemTraffic
import ZkFormal.NearV3.Assembly.RcptCandidateFinalTraffic
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


theorem located_final_view (tr : Trace Fp) (lists : List (List Input))
    (ls : RcptV3Vs) (h:flatR ls=locatedViews tr lists) :
    rcptRecvs3 ls B_FINAL=(receiptLocations 0 (entityPlans lists)).flatMap
      (fun x=>rRecvs x.2.receiptIndex (rcptOf tr 0 (inputShape x.1 x.2.input)) B_FINAL) := by
  have hh:=located_global_order ls 0 (fun r x=>rRecvs r x B_FINAL)
  simp only [Nat.zero_add] at hh
  rw [h,located_pairs,List.flatMap_map] at hh
  exact hh

theorem physical_finals (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw:∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh:2^log<Algebra.P)
    (pre post queryPost : PTrie) (rest : List (PTrie×PTrie)) (as : List AcctV)
    (ha:nativeAccountViews pre post (lists.flatten.map Input.receipt)=some as)
    (hn:(NearSpecV3.valsOf pre).length<Algebra.P) :
    let aid:=NativeReceiptAccountIds.accountId pre (lists.flatten.map Input.receipt)
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k aid constants) pub digests
      (completeReceiptAux ctx k lists aid (NativeReceiptAccessIds.accessId pre) fallback) headerFallback) 0
    ∀(hL:TableLocal receiptArithmeticCandidate tr 0 pub) (bs : List ListBlock) (e : Nat),
      ListChain tr 0 0 bs e→∀msg,
      tableBusCount RcptV3.interactions tr 0 pub B_FINAL false msg=
        (((accountLookupQueries (lists.flatten.map Input.receipt)++
          accessKeyLookupQueries (lists.flatten.map Input.receipt)).map
          (NativeQueryFinal.queryMessage ((pre,queryPost)::rest))).map Msg.toFp).count msg := by
  intro aid tr hL bs e hc msg
  have hf:=canonical_native_views own ctx lists log _ pub digests _ headerFallback hw hh hL bs e hc
  have hv:=located_final_view tr lists (bs.map (ListBlock.view tr 0)) hf
  have hm:(rcptRecvs3 (bs.map (ListBlock.view tr 0)) B_FINAL).Perm
      ((accountLookupQueries (lists.flatten.map Input.receipt)++accessKeyLookupQueries (lists.flatten.map Input.receipt)).map
        (NativeQueryFinal.queryMessage ((pre,queryPost)::rest))) := by
    rw [hv]
    have he:(receiptLocations 0 (entityPlans lists)).flatMap
        (fun x=>rRecvs x.2.receiptIndex (rcptOf tr 0 (inputShape x.1 x.2.input)) B_FINAL)=
        (receiptLocations 0 (entityPlans lists)).flatMap
        (fun x=>(receiptQueries x.2.input.receipt x.2.receiptIndex).map
          (NativeQueryFinal.queryMessage ((pre,queryPost)::rest))) := by
      apply ZkFormal.Near.Render.flatMap_congr'
      intro x hx
      obtain ⟨before,after,hb,hoff⟩:=native_locations_block lists x.1 x.2 hx
      have hp:=receipt_block_lookup lists x.2 before after hb 0 _ (receipt_first_position x.2)
      have hj:=planned_receipt_native_index lists x.2 ⟨sPL,0,4⟩ (List.mem_of_getElem? hp)
      rw [hoff]
      exact physical_final_inventory own ctx k lists log constants pub digests fallback headerFallback x.2 before after hb pre post queryPost rest _ as ha hn hj
    rw [he]
    simpa only [List.map_flatMap] using (located lists).map
      (NativeQueryFinal.queryMessage ((pre,queryPost)::rest))
  have ht:=ReceiptCandidateProof.ListChain.final_view_traffic hL hc false
  rw [tableBusCount_eq,ht]
  exact (hm.map Msg.toFp).count_eq msg
end ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
