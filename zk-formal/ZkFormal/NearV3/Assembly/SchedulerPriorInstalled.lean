import ZkFormal.NearV3.Assembly.SchedulerPriorOverlayIdJoins
import ZkFormal.NearV3.Assembly.SchedulerPriorOverlayExternal
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Checked selected-table installation; excludes full horizontal fusion,
shared comparison providers, and remaining external buses. -/
structure PriorInstalled (bs : List NativeBlock) : Prop where
  codec_local : ∀t pub,TableLocal (ProcPriorComparatorRoutedFamily.selected[8]!)
    (SchedHeight.trace (nativeBlockRows bs) codecPad) t pub
  overlay_local : ∀t pub,TableLocal (ProcPriorComparatorRoutedFamily.selected[19]!)
    (priorOverlay bs) t pub
  internal : ∀bus,bus∈[67,71,72,75]→∀t pub msg,
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub bus true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub bus false msg
  outgoing : ∀bus,bus∈[60,70]→∀t pub msg,
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] bus true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub bus false msg
  read : ∀t pub msg,
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 68 true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 68 false msg

theorem PriorCore.installed {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {bs : List NativeBlock} (hc:PriorCore p B bs)
    (hB:B≤2000000) :PriorInstalled bs := by
  refine ⟨?_,?_,?_,?_,routed_read_balance hp bs hc hB⟩
  · intro t pub
    exact (ProcPriorComparatorRouting.local_iff ProcPriorCodecActual.table _ t pub).mpr (hc.codec_local t pub)
  · intro t pub
    exact (ProcPriorComparatorRouting.local_iff ProcPriorCodecActualFamily.overlay _ t pub).mpr
      (overlay_local _ t pub (prior_overlay_local hp bs hc hB t pub))
  · intro bus hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl
    · exact routed_write_balance hp bs hc hB
    · exact routed_id_request_balance hp bs hc hB
    · exact routed_id_result_balance hp bs hc hB
    · exact routed_raw_record_balance hp bs hc hB
  · intro bus hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl
    · exact routed_presence_balance hp bs hc hB
    · exact routed_public_id_balance hp bs hc hB

/-- One accepted execution supplies the same blocks for all local constraints
and all seven joins in PriorInstalled. This is not whole-family HoldsP. -/
theorem accepted_prior_installed {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs,PriorCore p B bs ∧ PriorInstalled bs := by
  obtain ⟨bs,hc⟩:=accepted_prior_core hp hk hw h hB
  exact ⟨bs,hc,hc.installed hp hB⟩
end ZkFormal.NearV3.Assembly.CodecDigest
