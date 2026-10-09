import ZkFormal.NearV3.Candidates.ProcessRepairByteRange
import ZkFormal.NearV3.Candidates.ProcessRepairReceiptFinal
import ZkFormal.NearV3.Assembly.RcptCandidateBytesViewProof
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptByteRange
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open RcptV3Proof
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem projected {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub B_BYTES false msg=0)
    {id pos byte:Fp}
    (hc:0<tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_BYTES true [id,pos,byte]):
    byte.toNat<256:=by
  let msg:List Fp := [id,pos,byte]
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
  have hbus:(ProcPriorRoutedReceiptView.interaction i).bus=B_BYTES:=by
    unfold ProcPriorRoutedReceiptView.interaction;rw [hir];exact hb
  have hsend:(ProcPriorRoutedReceiptView.interaction i).send=true:=by
    unfold ProcPriorRoutedReceiptView.interaction;rw [hir];exact hs
  have hr0:r<tr.height 0:=hr
  have hp:=ZkFormal.Chacha.tableBusCount_pos hr0 hmem (by rw [hmult];exact hm)
  rw [hbus,hsend,hmsg] at hp
  have hle:=busCount_go_ge tr pub B_BYTES true msg AP.tables 0 0
    (show 0<AP.tables.length by rw [view.length];decide +kernel)
  simp only [Nat.zero_add] at hle
  apply ProcessRepairByteRange.sent view hpub
  change _≤busCount AP.toAir tr pub B_BYTES true msg at hle
  change 0<busCount AP.toAir tr pub B_BYTES true msg
  omega

theorem message {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub B_BYTES false msg=0)
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    {id pos byte:Nat} (hbyte:byte<P)
    (hm:[id,pos,byte]∈rcptSends3 pub (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)) B_BYTES):
    byte<256:=by
  have hp:0<tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_BYTES true
      [Fp.ofNat id,Fp.ofNat pos,Fp.ofNat byte]:=by
    rw [(Assembly.ReceiptCandidateProof.ListChain.bytes_view_traffic
      (Assembly.ReceiptCandidateProof.repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)) hc _).1,
      List.count_pos_iff]
    exact List.mem_map.mpr ⟨[id,pos,byte],hm,rfl⟩
  have hh:=projected view hpub hp
  simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt hbyte] using hh
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptByteRange
