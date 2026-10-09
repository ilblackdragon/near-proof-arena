import ZkFormal.NearV3.Candidates.ProcPriorRoutedNodeView
import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedVParent
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def send:Interaction:=HorizontalTables.interaction ProcPriorRoutedNodeView.offset (NodeV3.interactions[6]!)
def recv:Interaction:=HorizontalTables.interaction ProcPriorRoutedRawBytes.valueOffset (ValV3.interactions[2]!)

theorem filter_count (xs:List Interaction) (tr:Trace Fp) (t:Nat) (pub:List Fp)
    (bus:Nat) (dir:Bool) (msg:List Fp) :
    tableBusCount xs tr t pub bus dir msg=
      tableBusCount (xs.filter (fun i=>i.bus==bus && i.send==dir)) tr t pub bus dir msg := by
  rw [HorizontalTraffic.table_sum,HorizontalTraffic.table_sum]
  congr 1
  apply List.map_congr_left
  intro r hr
  unfold HorizontalTraffic.rowCount
  induction xs with
  | nil=>rfl
  | cons i xs ih=>
    by_cases hb:i.bus=bus <;> by_cases hs:i.send=dir <;>
      simp [hb,hs,ih]

theorem raw_send :ProcPriorComparatorRoutedFamily.raw.interactions.filter
    (fun i=>i.bus==B_VPARENT && i.send==true)=[send] := rfl

theorem raw_recv :ProcPriorComparatorRoutedFamily.raw.interactions.filter
    (fun i=>i.bus==B_VPARENT && i.send==false)=[recv] := rfl

theorem other_tables {AP:AirP} (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.bus≠B_VPARENT := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>i.bus != B_VPARENT)))=true := by decide +kernel
  intro t ht hn i hi
  rw [htables] at ht hi
  have hm:ProcPriorComparatorRoutedFamily.tables[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1 := by
    have he:(ProcPriorComparatorRoutedFamily.tables.drop 1)[t-1]?=some (ProcPriorComparatorRoutedFamily.tables[t]!) := by
      rw [List.getElem?_drop]
      have he:1+(t-1)=t := by omega
      rw [he,List.getElem?_eq_getElem ht]
      congr 1
      exact (getElem!_pos ProcPriorComparatorRoutedFamily.tables t ht).symm
    exact List.mem_iff_getElem?.mpr ⟨t-1,he⟩
  have hv:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i hi
  simpa using hv

theorem send_count (tr:Trace Fp) (pub msg:List Fp) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_VPARENT true msg=
      tableBusCount NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub B_VPARENT true msg := by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,filter_count,raw_send]
  have hbase:NodeV3.interactions.filter (fun i=>i.bus==B_VPARENT && i.send==true)=[NodeV3.interactions[6]!] := rfl
  rw [filter_count NodeV3.interactions, hbase]
  exact HorizontalTraffic.count_map (HorizontalTables.expression ProcPriorRoutedNodeView.offset)
    [NodeV3.interactions[6]!] tr (ProcPriorRoutedNodeView.node tr) 0 pub B_VPARENT true msg rfl
    (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r ProcPriorRoutedNodeView.offset pub e)

theorem recv_count (tr:Trace Fp) (pub msg:List Fp) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_VPARENT false msg=
      tableBusCount ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub B_VPARENT false msg := by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,filter_count,raw_recv]
  have hbase:ValV3.interactions.filter (fun i=>i.bus==B_VPARENT && i.send==false)=[ValV3.interactions[2]!] := rfl
  rw [filter_count ValV3.interactions,hbase]
  exact HorizontalTraffic.count_map (HorizontalTables.expression ProcPriorRoutedRawBytes.valueOffset)
    [ValV3.interactions[2]!] tr (ProcPriorRoutedRawBytes.value tr) 0 pub B_VPARENT false msg rfl
    (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r ProcPriorRoutedRawBytes.valueOffset pub e)

/-- The actual family's VPARENT balance relates exactly the projected Node
and Value views; no independent value witness or conditional conservation. -/
theorem balance {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    {vs:List NodeS3} {es:List ValE}
    (hN:ZkFormal.Near.TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs))
    (hV:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es)) :
    Link3.VParentBal vs es := by
  intro msg
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have hc (dir:Bool):busCount AP.toAir tr pub B_VPARENT dir msg=
      tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_VPARENT dir msg := by
    rw [busCount_single ht (fun t ht hn i hi hb=>(other_tables htables t ht hn i hi hb).elim)]
    rw [htables]
    rfl
  have hp (dir:Bool):pubCount AP pub B_VPARENT dir msg=0 :=
    pubCount_zero (fun seg hseg hb=>absurd hb (hpub seg hseg)) msg
  have hh:=hH.balance B_VPARENT msg
  rw [hc true,hc false,hp true,hp false,Nat.add_zero,Nat.add_zero,send_count,recv_count] at hh
  rw [(hN _ _).1,(hV _ _).2] at hh
  exact hh
end ZkFormal.NearV3.Candidates.ProcPriorRoutedVParent
