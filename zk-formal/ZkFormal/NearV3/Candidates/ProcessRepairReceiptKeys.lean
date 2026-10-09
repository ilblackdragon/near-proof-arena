import ZkFormal.NearV3.Candidates.ProcessRepairKeyView
import ZkFormal.NearV3.Candidates.ProcPriorReceiptKeySymbols
import ZkFormal.NearV3.Candidates.ProcPriorRoutedReceiptView
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeys
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open RcptV3Proof Assembly.ReceiptCandidateProof
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem inventory {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e) :
    ((List.range (tr.height 0)).flatMap
      (fun r=>ZkFormal.Near.rowTraffic RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 r pub B_KEYNIB true)).Perm
      ((rcptSends3 pub (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)) B_KEYNIB).map Msg.toFp) :=
  Assembly.ReceiptCandidateProof.ListChain.key_traffic
    (repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)) hc

theorem physical_symbols {AP:AirP} {pub msg:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hc:0<tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_KEYNIB true msg) :
    msg[2]!.toNat<16 ∨ msg[2]!.toNat=SYM_END := by
  have hL:=repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)
  obtain ⟨bs,e,hchain⟩:=extract_lists hL
  rw [(Assembly.ReceiptCandidateProof.ListChain.key_view_traffic hL hchain msg).1,
    List.count_pos_iff,List.mem_map] at hc
  obtain ⟨m,hm,he⟩:=hc
  have hb:=ProcPriorReceiptKeySymbols.chain_symbols hL hchain m hm
  subst msg
  have he:(Msg.toFp m)[2]!.toNat=m.getD 2 0:=by
    have hh:(Msg.toFp m)[2]! =Fp.ofNat (m.getD 2 0):=by
      cases m with
      | nil=>rfl
      | cons a m=>
        cases m with
        | nil=>rfl
        | cons b m=>cases m <;>rfl
    rw [hh,Fp.toNat_ofNat,Nat.mod_eq_of_lt hb.1]
  rw [he]
  exact hb.2
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeys
