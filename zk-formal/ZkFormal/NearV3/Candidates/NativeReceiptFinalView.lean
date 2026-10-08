import ZkFormal.NearV3.Candidates.NativeReceiptFinalCells
namespace ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly RcptSkeleton RcptV3 RcptV3Proof Rcpt.Candidates.NodePostUpdate

theorem query_zero (pre post : PTrie) (rest : List (PTrie×PTrie)) (wid : Nat) (key : List Nat) :
    NativeQueryFinal.queryMessage ((pre,post)::rest) ⟨wid,0,key⟩=
      NativeQueryFinal.message wid 0 (valueIndex pre key) := by
  simp [NativeQueryFinal.queryMessage,NativeQueryFinal.result,forestLookupVid,forestBytes]

theorem view_final (pre post : PTrie) (rest : List (PTrie×PTrie))
    (r : Receipt) (i : Nat) (x : RcptE)
    (ha:valueIndex pre (accountKeyPath r.receiverId)=some x.kslot)
    (he:x.ee=enabled r)
    (hf:x.akf=if (valueIndex pre (keyAccessKey r.receiverId r.signerPk)).isSome then FK_VAL else FK_ABS)
    (hk:x.akk=(valueIndex pre (keyAccessKey r.receiverId r.signerPk)).getD 0) :
    rRecvs i x B_FINAL=(receiptQueries r i).map (NativeQueryFinal.queryMessage ((pre,post)::rest)) := by
  cases hh:enabled r <;>
    simp [rRecvs,B_FINAL,B_DIGEST,he,hh,receiptQueries,account,access,query_zero,
      NativeQueryFinal.message,ha,hf,hk]

theorem physical_final_inventory (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (before after : List PlannedRow)
    (hb:plannedRows lists=before++plannedReceiptRows p++after)
    (pre post queryPost : PTrie) (rest : List (PTrie×PTrie)) (rs : List Receipt) (as : List AcctV)
    (ha:nativeAccountViews pre post rs=some as) (hn:(NearSpecV3.valsOf pre).length<Algebra.P)
    (hj:rs[p.receiptIndex]?=some p.input.receipt) :
    let aid:=NativeReceiptAccountIds.accountId pre rs
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k aid constants) pub digests
      (completeReceiptAux ctx k lists aid (NativeReceiptAccessIds.accessId pre) fallback) headerFallback) 0
    rRecvs p.receiptIndex (rcptOf tr 0 (inputShape before.length p.input)) B_FINAL=
      (receiptQueries p.input.receipt p.receiptIndex).map (NativeQueryFinal.queryMessage ((pre,queryPost)::rest)) := by
  intro aid tr
  have hs:=NativeReceiptAccountIds.slot_at ha p.receiptIndex p.input.receipt hj
  have hi:aid p<Algebra.P:=Nat.lt_trans (valueIndex_bound hs) hn
  have hk:(NativeReceiptAccessIds.accessId pre p).getD 0<Algebra.P:=by
    cases he:NativeReceiptAccessIds.accessId pre p with
    | none=>simp [he];decide
    | some n=>exact Nat.lt_trans (valueIndex_bound he) hn
  have hac:=physical_account_final own ctx k lists log constants pub digests aid (completeReceiptAux ctx k lists aid (NativeReceiptAccessIds.accessId pre) fallback) headerFallback p before after hb hi
  have hak:=physical_access_final own ctx k lists log (completeReceiptConstants ctx k aid constants) pub digests aid (NativeReceiptAccessIds.accessId pre) fallback headerFallback p before after hb hk
  apply view_final
  · change valueIndex pre (accountKeyPath p.input.receipt.receiverId)=some _
    rw [hac]
    exact hs
  · exact physical_enabled own ctx k lists log constants pub digests aid _ headerFallback p before after hb
  · exact hak.1
  · exact hak.2
end ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
