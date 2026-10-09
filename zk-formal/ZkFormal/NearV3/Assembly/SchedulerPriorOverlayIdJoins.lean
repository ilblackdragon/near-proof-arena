import ZkFormal.NearV3.Assembly.SchedulerPriorOverlayJoins
import ZkFormal.NearV3.Candidates.ProcIdTaggedTraffic
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem PriorCore.repaired_id_data {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {bs : List NativeBlock} (hc:PriorCore p B bs)
    (hB:B≤2000000) (req : Bool) (msg : List Fp) :
    componentCount bs 3 (if req then 71 else 72) req msg=
    componentCount bs 1 (if req then 71 else 72) (!req) msg := by
  have hpub:∀b∈bs,b.pub∈p.sched:=by
    intro b hb
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    exact List.mem_iff_getElem?.mpr ⟨i,(hc.indexed i b hi).1.1⟩
  have hn:∀b∈bs,b.pub.ids.length≤64:=fun b hb=>(prepD0_sched hp b.pub (hpub b hb)).n64
  have hraw:(ProcRawConcatGeometry.rows bs).length≤2001184:=by have :=hc.raw_bound;omega
  have hcap:=ProcNativeIdBalance.native_capacity (fun b=>b.pub.ids) bs hn hc.length hraw
  exact ProcIdTaggedTraffic.balance req (fun b=>b.pub.ids) bs (by omega) (Nat.le_of_lt hcap) 0 [] msg

/-- Both sides of the installed ID request bus count the same physical occurrences. -/
theorem routed_id_request_balance {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 71 true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 71 false msg := by
  apply Eq.trans (routed_overlay_other_count hp bs hc hB t pub 71 (by decide) (by decide) true msg)
  apply Eq.trans ?_ (routed_overlay_other_count hp bs hc hB t pub 71 (by decide) (by decide) false msg).symm
  simp only [source_sum]
  have z0true:=component_silent bs 0 71 true msg (by decide +kernel)
  have z0false:=component_silent bs 0 71 false msg (by decide +kernel)
  have z2true:=component_silent bs 2 71 true msg (by decide +kernel)
  have z2false:=component_silent bs 2 71 false msg (by decide +kernel)
  have z1true:=component_silent bs 1 71 true msg (by decide +kernel)
  have z3false:=component_silent bs 3 71 false msg (by decide +kernel)
  have hm:=hc.repaired_id_data hp hB true msg
  change componentCount bs 3 71 true msg=componentCount bs 1 71 false msg at hm
  omega

/-- Both sides of the installed ID result bus count the same physical occurrences. -/
theorem routed_id_result_balance {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 72 true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 72 false msg := by
  apply Eq.trans (routed_overlay_other_count hp bs hc hB t pub 72 (by decide) (by decide) true msg)
  apply Eq.trans ?_ (routed_overlay_other_count hp bs hc hB t pub 72 (by decide) (by decide) false msg).symm
  simp only [source_sum]
  have z0true:=component_silent bs 0 72 true msg (by decide +kernel)
  have z0false:=component_silent bs 0 72 false msg (by decide +kernel)
  have z2true:=component_silent bs 2 72 true msg (by decide +kernel)
  have z2false:=component_silent bs 2 72 false msg (by decide +kernel)
  have z1false:=component_silent bs 1 72 false msg (by decide +kernel)
  have z3true:=component_silent bs 3 72 true msg (by decide +kernel)
  have hm:=hc.repaired_id_data hp hB false msg
  change componentCount bs 3 72 false msg=componentCount bs 1 72 true msg at hm
  omega

end ZkFormal.NearV3.Assembly.CodecDigest
