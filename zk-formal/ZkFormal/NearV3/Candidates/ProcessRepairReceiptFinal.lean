import ZkFormal.NearV3.Candidates.ProcessRepairFinalSource
import ZkFormal.NearV3.Assembly.RcptCandidateFinalTraffic
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptFinal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open RcptV3Proof
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem query {AP:AirP} {pub msg:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub B_FINAL true msg=0)
    {ws:List WalkR} (hW:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    (hc:0<tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_FINAL false msg):
    ∃w∈ws,Msg.toFp [w.w,w.tau,w.fk,w.k]=msg:=by
  obtain ⟨r,hr,i,hi,hb,hs,he,hm⟩:=exists_of_tableBusCount (Nat.ne_of_gt hc)
  have hir:ProcPriorRoutedReceiptView.routed i=i:=by
    unfold ProcPriorRoutedReceiptView.routed ProcPriorComparatorRoutedFamily.route
    rw [if_neg (by rw [hb];decide)]
  have hmem:ProcPriorRoutedReceiptView.interaction i∈AP.tables[0]!.interactions:=by
    rw [view.wires];exact ProcPriorRoutedReceiptView.member hi
  have hmult:(ProcPriorRoutedReceiptView.interaction i).multNat tr 0 r pub=i.multNat (ProcPriorRoutedReceiptView.receipt tr) 0 r pub:=by
    unfold ProcPriorRoutedReceiptView.interaction
    rw [hir]
    exact HorizontalTraffic.mult_map _ _ tr (ProcPriorRoutedReceiptView.receipt tr) 0 r 0 pub
      (by intro e he;exact HorizontalTrace.expression_eval tr 0 r _ pub e)
  have hmsg:(ProcPriorRoutedReceiptView.interaction i).msgVal tr 0 r pub=msg:=by
    unfold ProcPriorRoutedReceiptView.interaction
    rw [hir]
    change (i.msg.map (HorizontalTables.expression ProcPriorRoutedReceiptView.offset)).map
      (fun e=>e.eval tr 0 r pub)=_
    rw [List.map_map]
    simpa only [Function.comp_def,HorizontalTrace.expression_eval,Interaction.msgVal,ProcPriorRoutedReceiptView.receipt] using he
  have hbus:(ProcPriorRoutedReceiptView.interaction i).bus=B_FINAL:=by
    unfold ProcPriorRoutedReceiptView.interaction;rw [hir];exact hb
  have hsend:(ProcPriorRoutedReceiptView.interaction i).send=false:=by
    unfold ProcPriorRoutedReceiptView.interaction;rw [hir];exact hs
  have hr0:r<tr.height 0:=hr
  obtain ⟨w,hw,heq⟩:=ProcessRepairFinalSource.received view hpub hW
    (show 0<AP.tables.length by rw [view.length];decide +kernel) hr0 hmem hbus hsend
    (by rw [hmult];exact hm)
  exact ⟨w,hw,heq.trans hmsg⟩

theorem record {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub B_FINAL true msg=0)
    {ws:List WalkR} (hW:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    {msg:Msg} (hm:msg∈rcptRecvs3 (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)) B_FINAL):
    ∃w∈ws,Msg.toFp [w.w,w.tau,w.fk,w.k]=Msg.toFp msg:=by
  apply query view hpub hW
  rw [ZkFormal.Near.tableBusCount_eq,Assembly.ReceiptCandidateProof.ListChain.final_traffic
    (Assembly.ReceiptCandidateProof.repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)) hc,
    List.count_pos_iff]
  exact List.mem_map.mpr ⟨msg,hm,rfl⟩
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptFinal
