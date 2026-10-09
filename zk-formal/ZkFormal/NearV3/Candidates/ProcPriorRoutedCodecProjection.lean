import ZkFormal.NearV3.Candidates.ProcPriorRoutedFamilyWrite
import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundRecordBound
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedCodecProjection
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def offset : Nat:=((ProcPriorComparatorRoutedFamily.selected.take 8).map (·.width)).sum
def codec (tr : Trace Fp) : Trace Fp:=HorizontalTrace.project offset tr
def interaction (i : Interaction) : Interaction:=HorizontalTables.interaction offset (ProcPriorComparatorRoutedFamily.route i)

theorem location :HorizontalTables.shifted offset (ProcPriorComparatorRoutedFamily.routeTable ProcPriorCodecActual.table)∈
    HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected := by
  have he:(HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected)[8]?=
    some (HorizontalTables.shifted offset (ProcPriorComparatorRoutedFamily.routeTable ProcPriorCodecActual.table)) := rfl
  exact List.mem_iff_getElem?.mpr ⟨8,he⟩

theorem projected_local {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:Local ProcPriorComparatorRoutedFamily.fused.constraints tr t pub) :
    ProcPriorCodecSoundRows.CLocal (codec tr) t pub := by
  change Local ProcPriorComparatorRoutedFamily.raw.constraints tr t pub at hL
  intro r hr e he
  unfold codec
  rw [←HorizontalTrace.expression_eval]
  exact hL r hr _ (List.mem_flatMap.mpr ⟨_,location,List.mem_map.mpr ⟨e,he,rfl⟩⟩)

theorem member {i : Interaction} (hi:i∈ProcPriorCodecActual.table.interactions)
    (hb:(ProcPriorComparatorRoutedFamily.route i).bus≠0) :
    interaction i∈ProcPriorComparatorRoutedFamily.fused.interactions := by
  classical
  have hraw:interaction i∈ProcPriorComparatorRoutedFamily.raw.interactions :=
    List.mem_flatMap.mpr ⟨_,location,List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,rfl⟩⟩
  have hpair:interaction i∈ProcPriorComparatorRoutedFamily.paired.interactions :=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  apply Classical.byContradiction
  intro hn
  have hall:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,j≠interaction i := by
    intro j hj he
    exact hn (he ▸ hj)
  have hd (b : Bool):InteractionTriples.dummy b≠interaction i := by
    intro he
    exact hb (congrArg Interaction.bus he).symm
  exact ((InteractionTriples.forall_iff _ (fun j=>j≠interaction i) (hd true) (hd false)).mp hall) _ hpair rfl

theorem message (i : Interaction) (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    (interaction i).msgVal tr t r pub=i.msgVal (codec tr) t r pub := by
  simp only [interaction,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  rw [ProcPriorComparatorRoutedFamily.route_payload]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r offset pub e

theorem mult (i : Interaction) (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    (interaction i).multNat tr t r pub=i.multNat (codec tr) t r pub := by
  unfold interaction Interaction.multNat
  simp only [HorizontalTables.interaction,ProcPriorComparatorRoutedFamily.route_mult]
  exact HorizontalTraffic.mult_map (HorizontalTables.expression offset) _ tr (codec tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r offset pub e)

theorem spar_none {AP : AirP} (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∀t,t<AP.tables.length→∀i∈AP.tables[t]!.interactions,i.bus=B_SPAR→i.send=false := by
  have hall:ProcPriorComparatorRoutedFamily.tables.all
      (fun T=>T.interactions.all (fun i=>i.bus != B_SPAR || !i.send))=true := by decide +kernel
  intro t ht i hi hb
  rw [htables] at ht hi
  have htmem:ProcPriorComparatorRoutedFamily.tables[t]!∈ProcPriorComparatorRoutedFamily.tables := by
    rw [getElem!_pos ProcPriorComparatorRoutedFamily.tables t ht]
    exact List.getElem_mem ht
  have hv:=List.all_eq_true.mp (List.all_eq_true.mp hall _ htmem) i hi
  simpa [hb] using hv
end ZkFormal.NearV3.Candidates.ProcPriorRoutedCodecProjection
