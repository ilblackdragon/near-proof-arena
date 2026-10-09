import ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedFamily
import ZkFormal.NearV3.Assembly.SchedulerRunSelected
namespace ZkFormal.NearV3.Candidates.ProcPriorProcessTransport
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorProcessRepairedFamily
set_option maxRecDepth 32768

theorem interaction_slot (i : Nat) : (selected[i]!).interactions=
    (ProcPriorComparatorRoutedFamily.selected[i]!).interactions := by
  by_cases hi:i=10
  · subst i
    rw [process_slot,Assembly.CodecDigest.routed_process_interactions]
  · rw [other_slot i hi]

theorem other_local (i : Nat) (hi:i≠10) (tr : Trace Fp) (t : Nat) (pub : List Fp) :
    TableLocal (selected[i]!) tr t pub ↔ TableLocal (ProcPriorComparatorRoutedFamily.selected[i]!) tr t pub := by
  rw [other_slot i hi]

theorem count (i : Nat) (tr : Trace Fp) (t : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) (msg : List Fp) :
    tableBusCount (selected[i]!).interactions tr t pub bus sd msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[i]!).interactions tr t pub bus sd msg := by
  rw [interaction_slot]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem raw_interactions : raw.interactions=ProcPriorComparatorRoutedFamily.raw.interactions := by decide +kernel

theorem paired_interactions : paired.interactions=ProcPriorComparatorRoutedFamily.paired.interactions := by
  change InteractionPairing.reorder raw.interactions=InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions
  rw [raw_interactions]

theorem fused_interactions : fused.interactions=ProcPriorComparatorRoutedFamily.fused.interactions := by
  change InteractionTriples.reorder paired.interactions=InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions
  rw [paired_interactions]
end ZkFormal.NearV3.Candidates.ProcPriorProcessTransport
