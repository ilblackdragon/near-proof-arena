import ZkFormal.NearV3.Candidates.ProcPriorRoutedQueueFinal
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedQueueKey
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open RcptV3Proof
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem binding {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpubKN:∀seg∈AP.pubSegs,seg.bus≠B_KEYNIB)
    (hpubF:∀msg,pubCount AP pub B_FINAL true msg=0)
    {bs:List ListBlock} {e:Nat}
    (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    (hcount:(bs.map fun B=>B.receipts.length).sum≤W_AK)
    (hK:(Qv.Candidates.CombinedTable.kPublic.eval (ProcPriorRoutedKeyView.key tr) 0 0 pub).toNat<64)
    {ws:List WalkR} (hW:WalkWf3 ws)
    (hWT:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    (q:Qv.Extract.WalkChain (ProcPriorRoutedKeyView.key tr) 0) (i:Nat) (hi:i<q.segs.length) :
    ∃w∈ws,w.key3=NearSpec.nibbles (Qv.Extract.physicalWalkBytes (ProcPriorRoutedKeyView.key tr) 0 q.segs[i]) ∧
      Msg.toFp [w.w,w.tau,w.fk,w.k]=Qv.Extract.finalMessage (ProcPriorRoutedKeyView.key tr) 0 q.segs[i].1 pub := by
  have hlen:(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length=
      (bs.map fun B=>B.receipts.length).sum:=by
    simp [flatR,List.flatMap_map,ListBlock.view,ListBlock.viewReceipts,List.length_flatMap,List.map_map]
  have hn:(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length≤W_AK:=by
    rwa [hlen]
  obtain ⟨w,hw,hfinal⟩:=ProcPriorRoutedQueueFinal.requested_walk hH htables hpubF hWT q i hi
  have hid:(w.w:Fp)=Qv.Candidates.CombinedTable.wid.eval (ProcPriorRoutedKeyView.key tr) 0 q.segs[i].1 pub:=
    congrArg (fun xs:List Fp=>xs.getD 0 0) hfinal
  have hk:=Qv.Extract.balanced_native_walk_key (ProcPriorRoutedKeyView.local_key hH htables) q i hi
    (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)) hn hK hW hw hid
    (ProcPriorRoutedKeyBalance.balance hH htables hpubKN hc hWT)
  exact ⟨w,hw,hk.2,hfinal⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedQueueKey
