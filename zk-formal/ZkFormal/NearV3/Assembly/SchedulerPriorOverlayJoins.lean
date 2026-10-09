import ZkFormal.NearV3.Assembly.SchedulerPriorRoutedTraffic
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorOverlayNativeSources

def componentCount (bs : List NativeBlock) (i bus : Nat) (sd : Bool) (msg : List Fp) : Nat :=
  tableBusCount (ProcPriorCodecActualFamily.components[i]!).interactions
    (priorSource bs i) 0 [] bus sd msg

theorem source_count (bs : List NativeBlock) (i bus : Nat) (sd : Bool) (msg : List Fp) :
    (ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) i bus sd).count msg=
    componentCount bs i bus sd msg := by
  unfold componentCount
  rw [tableBusCount_eq]
  have hh:(priorSource bs i).height 0=2^22:=by
    by_cases h0:i=0 <;> by_cases h1:i=1 <;> by_cases h2:i=2 <;>
      simp only [priorSource,h0,h1,h2,ite_true,ite_false] <;> rfl
  rw [hh]
  rfl

theorem component_silent (bs : List NativeBlock) (i bus : Nat) (sd : Bool) (msg : List Fp)
    (hz:((ProcPriorCodecActualFamily.components[i]!).interactions.all
      (fun a=> !(a.bus==bus && a.send==sd)))=true) :componentCount bs i bus sd msg=0 := by
  unfold componentCount
  rw [tableBusCount_eq]
  have row (r : Nat):rowTraffic (ProcPriorCodecActualFamily.components[i]!).interactions
      (priorSource bs i) 0 r [] bus sd=[] := by
    unfold rowTraffic
    apply List.flatMap_eq_nil_iff.mpr
    intro a ha
    have hn:=List.all_eq_true.mp hz a ha
    have hn':¬(a.bus=bus ∧ a.send=sd):=by
      intro ⟨hb,hs⟩
      simp [hb,hs] at hn
    simp only [ite_eq_right hn']
  simp only [row]
  have hz : (List.range ((priorSource bs i).height 0)).flatMap (fun _ => ([] : List (List Fp)))=[] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _=>rfl)
  rw [hz]
  rfl

theorem source_sum (bs : List NativeBlock) (bus : Nat) (sd : Bool) (msg : List Fp) :
    priorSourceCount bs bus sd msg=componentCount bs 0 bus sd msg+
      componentCount bs 1 bus sd msg+componentCount bs 2 bus sd msg+
      componentCount bs 3 bus sd msg := by
  unfold priorSourceCount
  simp only [source_count]

/-- Internal writes remain balanced after actual vertical installation and
comparison routing, for the same accepted block witness. -/
theorem routed_write_balance {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 67 true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 67 false msg := by
  apply Eq.trans (routed_overlay_other_count hp bs hc hB t pub 67 (by decide) (by decide) true msg)
  apply Eq.trans ?_ (routed_overlay_other_count hp bs hc hB t pub 67 (by decide) (by decide) false msg).symm
  simp only [source_sum]
  have z00:=component_silent bs 0 67 true msg (by decide +kernel)
  have z10:=component_silent bs 1 67 true msg (by decide +kernel)
  have z11:=component_silent bs 1 67 false msg (by decide +kernel)
  have z20:=component_silent bs 2 67 true msg (by decide +kernel)
  have z21:=component_silent bs 2 67 false msg (by decide +kernel)
  have z31:=component_silent bs 3 67 false msg (by decide +kernel)
  have hm:componentCount bs 3 67 true msg=componentCount bs 0 67 false msg :=
    (hc.memory_write 0 0 [] msg).symm
  omega
/-- Raw record bytes remain balanced after actual vertical installation and
comparison routing, for the same accepted block witness. -/
theorem routed_raw_record_balance {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 75 true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 75 false msg := by
  apply Eq.trans (routed_overlay_other_count hp bs hc hB t pub 75 (by decide) (by decide) true msg)
  apply Eq.trans ?_ (routed_overlay_other_count hp bs hc hB t pub 75 (by decide) (by decide) false msg).symm
  simp only [source_sum]
  have z00:=component_silent bs 0 75 true msg (by decide +kernel)
  have z01:=component_silent bs 0 75 false msg (by decide +kernel)
  have z10:=component_silent bs 1 75 true msg (by decide +kernel)
  have z11:=component_silent bs 1 75 false msg (by decide +kernel)
  have z21:=component_silent bs 2 75 false msg (by decide +kernel)
  have z30:=component_silent bs 3 75 true msg (by decide +kernel)
  have hm:componentCount bs 2 75 true msg=componentCount bs 3 75 false msg :=
    hc.raw_record 0 [] msg
  omega
end ZkFormal.NearV3.Assembly.CodecDigest
