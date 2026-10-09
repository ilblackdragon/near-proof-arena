import ZkFormal.NearV3.Candidates.ProcessRepairMemoryOrder
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open RcptV3Proof Link

theorem context {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubM:∀seg∈AP.pubSegs,seg.bus≠B_MEM) (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hv:ValWf es)
    (hV:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {as:List AcctV} (hwa:as=[] ∨ AcctV3Wf as)
    (ha:TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as))
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e):
    ProcessRepairMemoryOrder.Context pub
      ((flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).map RcptE.toRcptV) as:=by
  refine ⟨ProcessRepairMemoryNatural.permutation view hpubM hwa ha hc,
    ProcessRepairAccountUnique.slots view hpubV hv hV hwa ha,?_⟩
  intro r hr
  have hr':r<(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length:=by simpa using hr
  simpa only [List.getElem_map] using ProcessRepairReceiptWf.previous_le view hpubM hc r hr'

theorem authenticated {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubM:∀seg∈AP.pubSegs,seg.bus≠B_MEM) (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hv:ValWf es)
    (hV:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es)):
    ∃as:List AcctV,(as=[] ∨ AcctV3Wf as) ∧ TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as) ∧
    ∃bs:List ListBlock,∃e:Nat,ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e ∧
      ProcessRepairMemoryOrder.Context pub
        ((flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).map RcptE.toRcptV) as:=by
  obtain ⟨as,hwa,ha⟩:=ProcessRepairAccountView.accounts view
  have hL:=Assembly.ReceiptCandidateProof.repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)
  obtain ⟨bs,e,hc⟩:=Assembly.ReceiptCandidateProof.extract_lists hL
  exact ⟨as,hwa,ha,bs,e,hc,context view hpubM hpubV hv hV hwa ha hc⟩
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemory
