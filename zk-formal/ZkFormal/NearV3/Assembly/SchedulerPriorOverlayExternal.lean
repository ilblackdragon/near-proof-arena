import ZkFormal.NearV3.Assembly.SchedulerPriorOverlayJoins
import ZkFormal.NearV3.Assembly.SchedulerPriorPublicId
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem overlay_unique_count {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub : List Fp) (bus : Nat)
    (h69:bus≠69) (h40:bus≠40) (sd : Bool) (msg : List Fp) (i : Nat) (hi:i<4)
    (hz:∀j,j<4→j≠i→((ProcPriorCodecActualFamily.components[j]!).interactions.all
      (fun a=> !(a.bus==bus && a.send==sd)))=true) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub bus sd msg=componentCount bs i bus sd msg := by
  apply Eq.trans (routed_overlay_other_count hp bs hc hB t pub bus h69 h40 sd msg)
  simp only [source_sum]
  have h (j : Nat) (hj:j<4) (hne:j≠i):componentCount bs j bus sd msg=0:=
    component_silent bs j bus sd msg (hz j hj hne)
  have cases:i=0∨i=1∨i=2∨i=3:=by omega
  rcases cases with rfl|rfl|rfl|rfl
  · have :=h 1 (by decide) (by decide);have :=h 2 (by decide) (by decide);have :=h 3 (by decide) (by decide);omega
  · have :=h 0 (by decide) (by decide);have :=h 2 (by decide) (by decide);have :=h 3 (by decide) (by decide);omega
  · have :=h 0 (by decide) (by decide);have :=h 1 (by decide) (by decide);have :=h 3 (by decide) (by decide);omega
  · have :=h 0 (by decide) (by decide);have :=h 1 (by decide) (by decide);have :=h 2 (by decide) (by decide);omega

theorem routed_presence_balance {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 60 true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 60 false msg := by
  have ho:=overlay_unique_count hp bs hc hB t pub 60 (by decide) (by decide) false msg 2 (by decide) (by
    intro j hj hn
    have hh:j=0∨j=1∨j=3:=by omega
    rcases hh with rfl|rfl|rfl <;> decide +kernel)
  have hc0: tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 60 true msg=
      tableBusCount ProcPriorCodecActual.table.interactions
        (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 60 true msg := by
    exact ProcPriorComparatorRouting.other_count _ _ _ _ 60 (by decide) (by decide) _ _
  have hb:= hc.presence 0 [] msg
  have he:componentCount bs 2 60 false msg=
      tableBusCount ProcPriorCodecActual.table.interactions
        (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 60 true msg := hb.symm
  exact hc0.trans (he.symm.trans ho.symm)

theorem routed_read_balance {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 68 true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 68 false msg := by
  have ho:=overlay_unique_count hp bs hc hB t pub 68 (by decide) (by decide) true msg 0 (by decide) (by
    intro j hj hn
    have hh:j=1∨j=2∨j=3:=by omega
    rcases hh with rfl|rfl|rfl <;> decide +kernel)
  have hc0: tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 68 false msg=
      tableBusCount ProcPriorCodecActual.table.interactions
        (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 68 false msg := by
    exact ProcPriorComparatorRouting.other_count _ _ _ _ 68 (by decide) (by decide) _ _
  have hb:= hc.memory_read 0 0 [] msg
  have he:componentCount bs 0 68 true msg=
      tableBusCount ProcPriorCodecActual.table.interactions
        (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 68 false msg := hb
  exact ho.trans (he.trans hc0.symm)

theorem routed_public_id_balance {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 70 true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 70 false msg := by
  have ho:=overlay_unique_count hp bs hc hB t pub 70 (by decide) (by decide) false msg 1 (by decide) (by
    intro j hj hn
    have hh:j=0∨j=2∨j=3:=by omega
    rcases hh with rfl|rfl|rfl <;> decide +kernel)
  have hc0: tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 70 true msg=
      tableBusCount ProcPriorCodecActual.table.interactions
        (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 70 true msg := by
    exact ProcPriorComparatorRouting.other_count _ _ _ _ 70 (by decide) (by decide) _ _
  have hb:= hc.public_id hp hB 0 0 [] msg
  have he:componentCount bs 1 70 false msg=
      tableBusCount ProcPriorCodecActual.table.interactions
        (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 70 true msg := hb.symm
  exact hc0.trans (he.symm.trans ho.symm)

end ZkFormal.NearV3.Assembly.CodecDigest
