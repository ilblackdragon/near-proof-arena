import ZkFormal.NearV3.Candidates.ProcPriorRoutedNodeValueView
import ZkFormal.NearV3.Extract.HeadProof
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedHeadView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem table_eq :ProcPriorComparatorRoutedFamily.tables[1]! =InteractionTriples.table HeadV3.table := rfl

theorem local_head {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ZkFormal.Near.TableLocal HeadV3.table tr 1 pub := by
  have ht:1<AP.tables.length := by rw [htables];decide +kernel
  have htab:AP.tables[1]! =InteractionTriples.table HeadV3.table := by rw [htables];exact table_eq
  apply (InteractionTriples.local_iff HeadV3.table tr 1 pub).mp
  refine ⟨(hH.logBound 1 ht).1,?_,?_,?_⟩
  · have hh:tr.log 1≤AP.tables[1]!.maxLog := by
      rw [getElem!_pos AP.tables 1 ht]
      exact (hH.logBound 1 ht).2
    rwa [htab] at hh
  · intro r hr e he
    have hh:=local_of_holdsP hH ht r hr e
    rw [htab] at hh
    exact hh he
  · intro r hr i hi b hb
    rw [←htab,getElem!_pos AP.tables 1 ht] at hi
    exact hH.bits 1 ht r hr i hi b hb

theorem view {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∃hs:List HeadE,HeadWf hs ∧ ZkFormal.Near.TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs) :=
  head_view tr pub 1 (local_head hH htables)
end ZkFormal.NearV3.Candidates.ProcPriorRoutedHeadView
