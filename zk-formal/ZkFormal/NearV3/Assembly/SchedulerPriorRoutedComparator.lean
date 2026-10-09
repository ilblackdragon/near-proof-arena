import ZkFormal.NearV3.Assembly.SchedulerPriorComparator
import ZkFormal.NearV3.Assembly.SchedulerPriorOverlayJoins
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Sched.Complete ProcPriorComparisonRequests

theorem routed_comparator_selected :ProcPriorComparatorRoutedFamily.selected[12]! =Cmp.table B_SCMP := rfl

/-- Every actual installed prior comparison is received on shared bus40,
with its original multiplicity. All old standalone69 traffic is accounted for. -/
theorem routed_prior_comparison_count {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) t pub 40 true msg=((requests bs).map cmpMsg).count msg := by
  have hh:=routed_overlay_shared_count hp bs hc hB t pub true msg
  simp only [source_sum] at hh
  have z0:=component_silent bs 0 40 true msg (by decide +kernel)
  have z1:=component_silent bs 1 40 true msg (by decide +kernel)
  have z2:=component_silent bs 2 40 true msg (by decide +kernel)
  have z3:=component_silent bs 3 40 true msg (by decide +kernel)
  have z269:=component_silent bs 2 69 true msg (by decide +kernel)
  have z369:=component_silent bs 3 69 true msg (by decide +kernel)
  have hp0:componentCount bs 0 69 true msg+componentCount bs 1 69 true msg=
      ((requests bs).map cmpMsg).count msg :=prior_comparison_counts hp bs hc hB 0 0 [] msg
  omega

theorem routed_shared_comparator_local {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (old : List Request) (hok:∀q∈old,CmpOk q) (t : Nat) (pub : List Fp) :
    TableLocal (ProcPriorComparatorRoutedFamily.selected[12]!) (ProcSharedComparator.trace old bs) t pub :=
  shared_comparator_local hp bs hc hB old hok t pub

/-- Existing shared provider receives the old scheduler inventory plus all
actual installed prior traffic, on the same accepted blocks and fixed layout. -/
theorem routed_shared_comparator_balance {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (old : List Request) (hold:old.length≤3090136)
    (tc to : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[12]!).interactions
      (ProcSharedComparator.trace old bs) tc pub 40 false msg=
    (old.map cmpMsg).count msg+
      tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
        (priorOverlay bs) to pub 40 true msg := by
  have hb:=shared_comparator_balance hp bs hc hB old hold tc 0 0 pub msg
  have hpc:=prior_comparison_counts hp bs hc hB 0 0 pub msg
  have ho:=routed_prior_comparison_count hp bs hc hB to pub msg
  exact hb.trans (congrArg (fun n=>(old.map cmpMsg).count msg+n) (hpc.trans ho.symm))
end ZkFormal.NearV3.Assembly.CodecDigest
