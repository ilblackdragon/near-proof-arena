import ZkFormal.NearV3.Candidates.ProcPriorRoutedVParent
import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueNode
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedNodeValueView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched

/-- Extend an existing SAME-trace Value view by the actual installed Node
view and genuine VPARENT conservation. The caller's es is preserved. -/
theorem nodes_for_values {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    {es:List ValE}
    (hV:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es)) :
    ∃vs:List NodeS3,NodeWf3 vs ∧
      ZkFormal.Near.TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs) ∧
      Link3.VParentBal vs es := by
  obtain ⟨vs,hw,hN⟩:=ProcPriorRoutedNodeView.view hH htables
  exact ⟨vs,hw,hN,ProcPriorRoutedVParent.balance hH htables hpub hN hV⟩

theorem joined_views {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT) :
    ∃(vs:List NodeS3) (es:List ValE),NodeWf3 vs ∧ ValWf es ∧
      ZkFormal.Near.TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs) ∧
      ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es) ∧
      Link3.VParentBal vs es := by
  obtain ⟨es,hv,hV⟩:=ProcPriorRoutedValueView.view hH htables
  obtain ⟨vs,hn,hN,hbal⟩:=nodes_for_values hH htables hpub hV
  exact ⟨vs,es,hn,hv,hN,hV,hbal⟩

/-- One actual Node/Value extraction serves every present RawFrame byte and
its exact vid. No supplied NodeWf3, VParentBal, generated value list, or new
native value-ID allocation appears in this contract. -/
theorem raw_views {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hparent:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    (hbytes:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES) :
    ∃(vs:List NodeS3) (es:List ValE),NodeWf3 vs ∧ ValWf es ∧
      ZkFormal.Near.TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs) ∧
      ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es) ∧
      Link3.VParentBal vs es ∧
      ∀r,r<tr.height 0→cv (ProcPriorRoutedRawSource.raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1→
        cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.act=1→
        cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.present=1→
        let id:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.vid
        let pos:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.pos
        id<es.length ∧ es[id]!.vid=id ∧ pos<es[id]!.bytes.length ∧
          cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.byte=es[id]!.bytes.getD pos 0 := by
  obtain ⟨vs,es,hn,hv,hN,hV,hbal⟩:=joined_views hH htables hparent
  exact ⟨vs,es,hn,hv,hN,hV,hbal,fun _ hr hs ha hp=>
    ProcPriorRoutedValueBytes.raw_byte_index hH htables hbytes hv hV hr hs ha hp⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedNodeValueView
