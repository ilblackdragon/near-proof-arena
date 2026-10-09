import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueView
import ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedKeyView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def offset:Nat:=((ProcPriorComparatorRoutedFamily.selected.take 18).map (·.width)).sum
def key (tr:Trace Fp):Trace Fp:=HorizontalTrace.project offset tr
def routed (i:Interaction):Interaction:=ProcPriorComparatorRoutedFamily.route i
def interaction (i:Interaction):Interaction:=HorizontalTables.interaction offset (routed i)

theorem location :HorizontalTables.shifted offset
    (ProcPriorComparatorRoutedFamily.routeTable Qv.Candidates.KeyTrafficRepair.table)∈
    HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected := by
  have he:(HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected)[18]?=
    some (HorizontalTables.shifted offset
      (ProcPriorComparatorRoutedFamily.routeTable Qv.Candidates.KeyTrafficRepair.table)) := rfl
  exact List.mem_iff_getElem?.mpr ⟨18,he⟩

theorem constraint_member {e:Expr} (he:e∈Qv.Candidates.CombinedTable.constraints) :
    HorizontalTables.expression offset e∈ProcPriorComparatorRoutedFamily.fused.constraints := by
  change _∈ProcPriorComparatorRoutedFamily.raw.constraints
  apply List.mem_flatMap.mpr
  refine ⟨_,location,List.mem_map.mpr ⟨e,?_,rfl⟩⟩
  exact he

theorem mult_eq (i:Interaction):(routed i).mult=i.mult := by
  exact ProcPriorComparatorRoutedFamily.route_mult i

theorem member {i:Interaction} (hi:i∈Qv.Candidates.KeyTrafficRepair.interactions) :
    interaction i∈ProcPriorComparatorRoutedFamily.fused.interactions := by
  classical
  have hraw:interaction i∈ProcPriorComparatorRoutedFamily.raw.interactions := by
    apply List.mem_flatMap.mpr
    refine ⟨_,location,List.mem_map.mpr ⟨routed i,?_,rfl⟩⟩
    exact List.mem_map.mpr ⟨i,hi,rfl⟩
  have hp:interaction i∈ProcPriorComparatorRoutedFamily.paired.interactions :=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  have hallmult:Qv.Candidates.KeyTrafficRepair.interactions.all (fun j=>decide (0<j.mult.length))=true := by decide +kernel
  have hb:0<i.mult.length := by simpa using List.all_eq_true.mp hallmult i hi
  apply Classical.byContradiction
  intro hn
  have hall:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,j≠interaction i := by
    intro j hj he;exact hn (he ▸ hj)
  have hd (b:Bool):InteractionTriples.dummy b≠interaction i := by
    intro he
    have hh:=congrArg (fun j:Interaction=>j.mult.length) he
    change 0=((routed i).mult.map (HorizontalTables.expression offset)).length at hh
    rw [List.length_map,mult_eq] at hh
    omega
  exact ((InteractionTriples.forall_iff _ (fun j=>j≠interaction i) (hd true) (hd false)).mp hall) _ hp rfl

/-- Repaired queue key legality on the actual installed slot18 projection. -/
theorem local_key {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ZkFormal.Near.TableLocal Qv.Candidates.KeyTrafficRepair.table (key tr) 0 pub := by
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have htab:AP.tables[0]! =ProcPriorComparatorRoutedFamily.fused := by rw [htables];rfl
  refine ⟨(hH.logBound 0 ht).1,?_,?_,?_⟩
  · have hh:tr.log 0≤AP.tables[0]!.maxLog := by
      rw [getElem!_pos AP.tables 0 ht]
      exact (hH.logBound 0 ht).2
    rw [htab] at hh
    exact hh
  · intro r hr e he
    have hh:=local_of_holdsP hH ht r hr (HorizontalTables.expression offset e)
    rw [htab] at hh
    have heq:=hh (constraint_member he)
    rw [HorizontalTrace.expression_eval] at heq
    exact heq
  · intro r hr i hi b hb
    have him:interaction i∈AP.tables[0]!.interactions := by rw [htab];exact member hi
    have hbm:HorizontalTables.expression offset b∈(interaction i).mult := by
      change _∈(routed i).mult.map (HorizontalTables.expression offset)
      rw [mult_eq]
      exact List.mem_map.mpr ⟨b,hb,rfl⟩
    rw [getElem!_pos AP.tables 0 ht] at him
    have hh:=hH.bits 0 ht r hr _ him _ hbm
    rw [HorizontalTrace.expression_eval] at hh
    exact hh

end ZkFormal.NearV3.Candidates.ProcPriorRoutedKeyView
