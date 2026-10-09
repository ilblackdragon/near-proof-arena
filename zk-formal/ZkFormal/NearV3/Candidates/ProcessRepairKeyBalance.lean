import ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeys
import ZkFormal.NearV3.Candidates.ProcessRepairKeySource
namespace ZkFormal.NearV3.Candidates.ProcessRepairKeyBalance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open RcptV3Proof Assembly.ReceiptCandidateProof
theorem balance {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_KEYNIB)
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    {ws:List WalkR} (hW:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws)) :
    ((List.range (tr.height 0)).flatMap (fun r=>ZkFormal.Near.rowTraffic Qv.Candidates.KeyTrafficRepair.interactions
      (ProcPriorRoutedKeyView.key tr) 0 r pub B_KEYNIB true) ++
      (rcptSends3 pub (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)) B_KEYNIB).map Msg.toFp).Perm
      ((walkRecvs3 ws B_KEYNIB).map Msg.toFp) := by
  apply List.perm_iff_count.mpr
  intro msg
  have hp (dir:Bool):pubCount (ProcessRepairBalance.reference AP) pub B_KEYNIB dir msg=0:=
    pubCount_zero (fun seg hs hb=>absurd hb (hpub seg hs)) msg
  have hh:=ProcessRepairBalance.balance view B_KEYNIB msg
  rw [hp true,hp false,Nat.add_zero,Nat.add_zero,ProcPriorRoutedKeyCounts.global_count (AP:=ProcessRepairBalance.reference AP) rfl,
    ProcPriorRoutedKeyBalance.global_recv (AP:=ProcessRepairBalance.reference AP) rfl,(hW B_KEYNIB msg).2] at hh
  have hL:=repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)
  rw [(Assembly.ReceiptCandidateProof.ListChain.key_view_traffic hL hc msg).1,ZkFormal.Near.tableBusCount_eq] at hh
  simp only [List.count_append]
  change _=_ at hh
  simpa only [walkTraffic3,Nat.add_comm,ProcPriorRoutedKeyView.key,HorizontalTrace.project,Trace.height] using hh
end ZkFormal.NearV3.Candidates.ProcessRepairKeyBalance
