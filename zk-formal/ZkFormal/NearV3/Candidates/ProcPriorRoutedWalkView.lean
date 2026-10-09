import ZkFormal.NearV3.Candidates.ProcPriorRoutedNodeValueView
import ZkFormal.NearV3.Extract.WalkProof2
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedWalkView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem table_eq :ProcPriorComparatorRoutedFamily.tables[2]! =InteractionTriples.table WalkV3.table := rfl

theorem local_walk {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ZkFormal.Near.TableLocal WalkV3.table tr 2 pub := by
  have ht:2<AP.tables.length := by rw [htables];decide +kernel
  have htab:AP.tables[2]! =InteractionTriples.table WalkV3.table := by rw [htables];exact table_eq
  apply (InteractionTriples.local_iff WalkV3.table tr 2 pub).mp
  refine ⟨(hH.logBound 2 ht).1,?_,?_,?_⟩
  · have hh:tr.log 2≤AP.tables[2]!.maxLog := by
      rw [getElem!_pos AP.tables 2 ht]
      exact (hH.logBound 2 ht).2
    rwa [htab] at hh
  · intro r hr e he
    have hh:=local_of_holdsP hH ht r hr e
    rw [htab] at hh
    exact hh he
  · intro r hr i hi b hb
    rw [←htab,getElem!_pos AP.tables 2 ht] at hi
    exact hH.bits 2 ht r hr i hi b hb

theorem view {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∃hs:List WalkR,WalkWf3 hs ∧ (hs.flatMap (·.steps)).length≤2^21 ∧ ZkFormal.Near.TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 hs) :=
  walk3_view tr pub 2 (local_walk hH htables)
end ZkFormal.NearV3.Candidates.ProcPriorRoutedWalkView
