import ZkFormal.NearV3.Assembly.SchedulerPriorOverlayTraffic
import ZkFormal.NearV3.Assembly.SchedulerPriorRoutedOverlay
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorOverlayNativeSources

def priorSourceCount (bs : List NativeBlock) (bus : Nat) (sd : Bool) (msg : List Fp) : Nat :=
  (ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 0 bus sd).count msg+
  (ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 1 bus sd).count msg+
  (ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 2 bus sd).count msg+
  (ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 3 bus sd).count msg

/-- Installing the repaired comparator routing preserves every other bus,
including each physical occurrence in the same accepted witness. -/
theorem routed_overlay_other_count {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub : List Fp) (bus : Nat)
    (h69:bus≠69) (h40:bus≠40) (sd : Bool) (msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub bus sd msg=priorSourceCount bs bus sd msg := by
  change tableBusCount (ProcPriorCodecActualFamily.overlay.interactions.map
    ProcPriorComparatorRoutedFamily.route) _ _ _ _ _ _=_
  rw [ProcPriorComparatorRouting.other_count _ _ _ _ _ h69 h40]
  exact native_overlay_count hp bs hc hB t pub bus sd msg

/-- Shared comparator traffic is the sum of original40 and prior69 requests;
there is no deduplication or independently chosen component witness. -/
theorem routed_overlay_shared_count {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub : List Fp) (sd : Bool) (msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 40 sd msg=
      priorSourceCount bs 40 sd msg+priorSourceCount bs 69 sd msg := by
  change tableBusCount (ProcPriorCodecActualFamily.overlay.interactions.map
    ProcPriorComparatorRoutedFamily.route) _ _ _ _ _ _=_
  rw [ProcPriorComparatorRouting.shared_count]
  rw [native_overlay_count hp bs hc hB,native_overlay_count hp bs hc hB]
  rfl
end ZkFormal.NearV3.Assembly.CodecDigest
