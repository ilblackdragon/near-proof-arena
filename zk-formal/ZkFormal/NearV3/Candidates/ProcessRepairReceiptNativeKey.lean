import ZkFormal.NearV3.Candidates.ProcessRepairReceiptReceiverShape
import ZkFormal.NearV3.Candidates.ProcessRepairQueuePublic
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptNativeKey
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open RcptV3Proof

theorem key {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_KEYNIB)
    {bs:List ListBlock} {e:Nat}
    (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    (hn:(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length≤W_AK)
    {ws:List WalkR} (hW:WalkWf3 ws)
    (hWT:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    {w:WalkR} (hw:w∈ws)
    (hr:w.w<(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length):
    w.key3=NearSpec.accountKeyPath (toBytes
      ((flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).getD w.w default).v):=by
  let x:=((flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).getD w.w default)
  have hx:x∈flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)):=by
    simp only [x,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hr]
    exact List.getElem_mem hr
  obtain ⟨hb,_,hsize,_⟩:=ProcessRepairReceiptReceiverShape.receiver view hc hx
  obtain ⟨hlen,hcanon,hkey⟩:=ProcessRepairReceiptReceiverShape.native_key x hb hsize
  have hs:=ProcessRepairReceiptWalkKey.symbols hW hw x.keySyms hlen hcanon
    (ProcessRepairReceiptKeyOwner.walk_messages view hpub hc hn hWT hw hr)
  exact hs.2.trans hkey

theorem prepared {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpubKN:∀seg∈AP.pubSegs,seg.bus≠B_KEYNIB)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (overhead:Nat)
    (hpub:pub=ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))
    {bs:List ListBlock} {e:Nat}
    (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    {ws:List WalkR} (hW:WalkWf3 ws)
    (hWT:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    {w:WalkR} (hw:w∈ws)
    (hr:w.w<(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length):
    w.key3=NearSpec.accountKeyPath (toBytes
      ((flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).getD w.w default).v):=by
  apply key view hpubKN hc _ hW hWT hw hr
  have hn:=(ProcessRepairQueuePublic.receipt_count hp overhead (hpub ▸ view) hc).2
  simpa [flatR,List.flatMap_map,ListBlock.view,ListBlock.viewReceipts,List.length_flatMap,List.map_map] using hn
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptNativeKey
