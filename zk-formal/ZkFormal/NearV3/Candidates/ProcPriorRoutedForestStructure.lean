import ZkFormal.NearV3.Candidates.ProcPriorRoutedParent
import ZkFormal.NearV3.Link.Compose3
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedForestStructure
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched

/-- Every actual extracted node belongs to an actual Head instance and has
non-wrapping depth below 400, from installed PARENT conservation. -/
theorem heads_for_nodes {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hparent:∀seg∈AP.pubSegs,seg.bus≠ZkFormal.Near.B_PARENT)
    {vs:List NodeS3} (hw:NodeWf3 vs)
    (hN:ZkFormal.Near.TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs)) :
    ∃hs:List HeadE,HeadWf hs ∧
      ZkFormal.Near.TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs) ∧
      Link3.ParentBal vs hs ∧
      (∀n (hn:n<vs.length),vs[n].depth<400 ∧ ∃h,h∈hs ∧ h.tau=vs[n].tau) ∧
      (∀h,h∈hs→∃hr:h.rid<vs.length,vs[h.rid].tau=h.tau ∧ vs[h.rid].depth=0 ∧
        (vs[h.rid].v.ser false).length%P=h.rlen ∧ vs[h.rid].res=h.rres) := by
  obtain ⟨hs,hh,hT⟩:=ProcPriorRoutedHeadView.view hH htables
  have hb:=ProcPriorRoutedParent.balance hH htables hparent hN hT
  exact ⟨hs,hh,hT,hb,
    fun n hn=>⟨Link3.depth_lt hw hh hb hn,Link3.head_of hw hh hb n hn⟩,
    fun h hm=>Link3.head_link hw hh hb hm⟩

/-- Actual Node, Value and Head views share both structural buses. The
remaining root-authentication work is SHA/ROOT/UPS ownership, not an assumed
node-parent relation or independently chosen forest witness. -/
theorem views {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hparent:∀seg∈AP.pubSegs,seg.bus≠ZkFormal.Near.B_PARENT)
    (hvparent:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT) :
    ∃(vs:List NodeS3) (es:List ValE) (hs:List HeadE),NodeWf3 vs ∧ ValWf es ∧ HeadWf hs ∧
      ZkFormal.Near.TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs) ∧
      ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es) ∧
      ZkFormal.Near.TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs) ∧
      Link3.VParentBal vs es ∧ Link3.ParentBal vs hs ∧
      (∀n (hn:n<vs.length),vs[n].depth<400 ∧ ∃h,h∈hs ∧ h.tau=vs[n].tau) := by
  obtain ⟨vs,es,hn,hv,hN,hV,hvb⟩:=ProcPriorRoutedNodeValueView.joined_views hH htables hvparent
  obtain ⟨hs,hh,hT,hpb,hdepth,_⟩:=heads_for_nodes hH htables hparent hn hN
  exact ⟨vs,es,hs,hn,hv,hh,hN,hV,hT,hvb,hpb,hdepth⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedForestStructure
