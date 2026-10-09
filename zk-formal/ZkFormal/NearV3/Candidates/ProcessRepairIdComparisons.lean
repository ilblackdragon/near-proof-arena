import ZkFormal.NearV3.Candidates.ProcessRepairComparatorSound
import ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyLastWrite
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdComparisons
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def request (j : Nat) :Interaction :=HorizontalTables.interaction ProcPriorCodecFamilyRead.offset
  (ProcPriorComparatorRoutedFamily.route (ProcPriorVertical4Linear.interaction 1 (ProcPriorIdTable.interactions 70 71 72 69)[j]!))

theorem request_member (j : Nat) (hj:j=3 ∨ j=4 ∨ j=5 ∨ j=6) :request j∈ProcPriorComparatorRoutedFamily.fused.interactions := by
  classical
  have hloc:HorizontalTables.shifted ProcPriorCodecFamilyRead.offset
      (ProcPriorComparatorRoutedFamily.routeTable ProcPriorCodecActualFamily.overlay)∈
      HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected := by
    have he:(HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected)[19]?=
      some (HorizontalTables.shifted ProcPriorCodecFamilyRead.offset
        (ProcPriorComparatorRoutedFamily.routeTable ProcPriorCodecActualFamily.overlay)) := rfl
    exact List.mem_iff_getElem?.mpr ⟨19,he⟩
  have hbase:(ProcPriorIdTable.interactions 70 71 72 69)[j]!∈ProcPriorIdTable.interactions 70 71 72 69 := by
    have hb:j<(ProcPriorIdTable.interactions 70 71 72 69).length := by rcases hj with rfl|rfl|rfl|rfl <;> decide
    rw [getElem!_pos (ProcPriorIdTable.interactions 70 71 72 69) j hb]
    exact List.getElem_mem hb
  have hover:ProcPriorVertical4Linear.interaction 1 (ProcPriorIdTable.interactions 70 71 72 69)[j]!∈
      ProcPriorCodecActualFamily.overlay.interactions := by
    apply List.mem_flatMap.mpr
    refine ⟨(ProcPriorIdTable.table 70 71 72 69,1),by simp [ProcPriorCodecActualFamily.components,ProcPriorVertical4Linear.components,List.zipIdx],?_⟩
    exact List.mem_map.mpr ⟨_,hbase,rfl⟩
  have hraw:request j∈ProcPriorComparatorRoutedFamily.raw.interactions :=
    List.mem_flatMap.mpr ⟨_,hloc,List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨_,hover,rfl⟩,rfl⟩⟩
  have hpair:request j∈ProcPriorComparatorRoutedFamily.paired.interactions :=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  apply Classical.byContradiction
  intro hn
  have hall:∀i∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,i≠request j := by
    intro i hi he
    exact hn (he ▸ hi)
  have hd (b : Bool):InteractionTriples.dummy b≠request j := by
    intro he
    have hb:=congrArg Interaction.bus he
    rcases hj with rfl|rfl|rfl|rfl <;> change 0=40 at hb <;> omega
  exact ((InteractionTriples.forall_iff _ (fun i=>i≠request j) (hd true) (hd false)).mp hall) _ hpair rfl

theorem request_message (j : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    (request j).msgVal tr t r pub=
      (ProcPriorVertical4Linear.interaction 1 (ProcPriorIdTable.interactions 70 71 72 69)[j]!).msgVal (memory tr) t r pub := by
  simp only [request,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  rw [ProcPriorComparatorRoutedFamily.route_payload]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r ProcPriorCodecFamilyRead.offset pub e

theorem request_mult (j : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    (request j).multNat tr t r pub=
      (ProcPriorVertical4Linear.interaction 1 (ProcPriorIdTable.interactions 70 71 72 69)[j]!).multNat (memory tr) t r pub := by
  unfold request Interaction.multNat
  simp only [HorizontalTables.interaction,ProcPriorComparatorRoutedFamily.route_mult]
  exact HorizontalTraffic.mult_map (HorizontalTables.expression ProcPriorCodecFamilyRead.offset) _ tr (memory tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r ProcPriorCodecFamilyRead.offset pub e)

theorem compare {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40) (j : Nat) (hj:j=3∨j=4∨j=5∨j=6)
    {r : Nat} (hr:r<tr.height 0) (hm:(request j).multNat tr 0 r pub≠0)
    {x y : Fp} (hmsg:(request j).msgVal tr 0 r pub=[x,y,1])
    (hx:x.toNat<2^29) (hy:y.toNat<2^29) :y.toNat≤x.toNat := by
  have ht:0<AP.tables.length := by rw [view.length];decide +kernel
  have hi:request j∈AP.tables[0]!.interactions := by
    rw [view.wires];exact request_member j hj
  have hb:(request j).bus=40 := by rcases hj with rfl|rfl|rfl|rfl <;> rfl
  have hs:(request j).send=true := by rcases hj with rfl|rfl|rfl|rfl <;> rfl
  exact ProcessRepairComparatorSound.prior_ge view hpub ht hr hi hb hs hm hmsg hx hy
end ZkFormal.NearV3.Candidates.ProcessRepairIdComparisons
