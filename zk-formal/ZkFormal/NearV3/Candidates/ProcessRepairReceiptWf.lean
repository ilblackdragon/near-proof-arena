import ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemProvider
import ZkFormal.NearV3.Assembly.RcptCandidateTableTokens
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptWf
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open RcptV3Proof

theorem count_bound {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) {bs:List ListBlock} {e:Nat}
    (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e):
    (flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length≤2^22:=by
  have hL:=Assembly.ReceiptCandidateProof.repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)
  have hlog:tr.log 0≤22:=hL.log_le
  have hh:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) hlog
  have hrows:=hc.rows
  have hpad:=hc.end_padding.1
  have hn:=Assembly.ReceiptCandidateProof.receipt_counts_le_rows bs
  have heq:(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length=
      (bs.map fun B=>B.receipts.length).sum:=by
    simp [flatR,List.flatMap_map,ListBlock.view,ListBlock.viewReceipts,List.length_flatMap,List.map_map]
  rw [heq]
  change e<tr.height 0 at hpad
  omega

theorem tokens {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_MEM)
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e):
    let ls:=bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)
    ∃toks:List Nat,toks.length=(flatR ls).length+1 ∧ toks.head?=some 0 ∧
      (∀r,(hr:r<(flatR ls).length)→(flatR ls)[r].Wf r (pubBytes pub PH_GP 16)
        (toks.getD r 0) (toks.getD (r+1) 0)) ∧
      ((∀i,i<16→pubNat pub (PH_BURNT+i)<256)→
        toks.getD (flatR ls).length 0=leN' (pubBytes pub PH_BURNT 16)):=by
  have hL:=Assembly.ReceiptCandidateProof.repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)
  apply Assembly.ReceiptCandidateProof.ListChain.view_tokens hL hc
  intro B hB y hy
  have hx:rcptOf (ProcPriorRoutedReceiptView.receipt tr) 0 y∈
      flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)):=by
    apply List.mem_flatMap.mpr
    refine ⟨B.view (ProcPriorRoutedReceiptView.receipt tr) 0,List.mem_map.mpr ⟨B,hB,rfl⟩,?_⟩
    exact List.mem_map.mpr ⟨y,hy,rfl⟩
  exact Nat.le_trans (ProcessRepairReceiptMemProvider.previous view hpub hc hx) (count_bound view hc)

theorem previous_le {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_MEM)
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    (r:Nat) (hr:r<(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length):
    (flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)))[r].tprev≤r:=by
  obtain ⟨toks,_,_,hw,_⟩:=tokens view hpub hc
  apply (hw r hr).tprev_le
  have hp:=ProcessRepairReceiptMemProvider.previous view hpub hc (List.getElem_mem hr)
  have hc:=count_bound view hc
  unfold P
  omega
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptWf
