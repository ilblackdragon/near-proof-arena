import ZkFormal.NearV3.Candidates.ProcPriorRoutedRawBytes
import ZkFormal.NearV3.Extract.ValProof
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedValueView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedRawBytes
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem location :HorizontalTables.shifted valueOffset
    (ProcPriorComparatorRoutedFamily.routeTable Rcpt.Candidates.EmptyValueFusion.valueTable)∈
    HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected := by
  have he:(HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected)[5]?=
    some (HorizontalTables.shifted valueOffset
      (ProcPriorComparatorRoutedFamily.routeTable Rcpt.Candidates.EmptyValueFusion.valueTable)) := rfl
  exact List.mem_iff_getElem?.mpr ⟨5,he⟩

theorem constraint_member {e:Expr} (he:e∈ValV3.constraints) :
    HorizontalTables.expression valueOffset e∈ProcPriorComparatorRoutedFamily.fused.constraints := by
  change _∈ProcPriorComparatorRoutedFamily.raw.constraints
  apply List.mem_flatMap.mpr
  refine ⟨_,location,List.mem_map.mpr ⟨e,?_,rfl⟩⟩
  change e∈(ValV3.constraints++Rcpt.Candidates.SizeCount.countConstraints _ _)++_
  exact List.mem_append_left _ (List.mem_append_left _ he)

theorem bool_mult (i:Interaction) (hi:i∈ValV3.interactions) (b:Expr) (hb:b∈i.mult) :
    ZkFormal.Near.Dsl.bool b∈ValV3.constraints := by
  simp only [ValV3.interactions,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals change b∈[_] at hb
  all_goals rw [List.mem_singleton] at hb
  all_goals subst b
  all_goals simp [ValV3.constraints]

/-- The installed slot5 retains the complete original Value constraints.
Base multiplicity booleans are also retained constraints, so its TableLocal
is obtained on exactly the horizontally projected physical trace. -/
theorem local_value {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ZkFormal.Near.TableLocal ValV3.table (value tr) 0 pub := by
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have htab:AP.tables[0]! =ProcPriorComparatorRoutedFamily.fused := by rw [htables];rfl
  have hcon:∀r,r<(value tr).height 0→∀e∈ValV3.constraints,e.eval (value tr) 0 r pub=0 := by
    intro r hr e he
    have hh:=local_of_holdsP hH ht r hr (HorizontalTables.expression valueOffset e)
    rw [htab] at hh
    have heq:=hh (constraint_member he)
    rw [HorizontalTrace.expression_eval] at heq
    exact heq
  refine ⟨(hH.logBound 0 ht).1,?_,hcon,?_⟩
  · have hh:tr.log 0≤AP.tables[0]!.maxLog := by
      rw [getElem!_pos AP.tables 0 ht]
      exact (hH.logBound 0 ht).2
    rw [htab] at hh
    exact hh
  · intro r hr i hi b hb
    have hh:=hcon r hr _ (bool_mult i hi b hb)
    rw [ZkFormal.Near.eval_bool] at hh
    exact ZkFormal.Near.bool_cases hh

/-- A canonical Value list and all original Value traffic are extracted from
the actual installed component, without a supplied/generated value list. -/
theorem view {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∃es:List ValE,ValWf es ∧ ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es) :=
  ZkFormal.NearV3.val_view (value tr) pub 0 (local_value hH htables)
end ZkFormal.NearV3.Candidates.ProcPriorRoutedValueView
