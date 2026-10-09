import ZkFormal.NearV3.Rcpt.Candidates.NativeCountOwnership
import ZkFormal.NearV3.Rcpt.Candidates.RetainedStorePayload
import ZkFormal.NearV3.Rcpt.Candidates.UniqPayload

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near ZkFormal.Algebra NearSpec NearSpecV3 Link3 Assembly

/-- Actual uniqueness/SHA/parent buses pay every retained native byte with a
nonduplicate SIZE payload representative. No weighted coverage premise remains. -/
theorem native_payload_from_uniqueness (k : WalkD0) (x : ExtV3)
    {us : List UniqE} {others : List Msg} {shaS shaR : Nat → List Fp → Nat}
    (hw : NodeWf3 x.nodes) (hhw : HeadWf x.heads) (hvw : ValWf x.values) (huw : UniqWf us)
    (hb : ParentBal x.nodes x.heads) (hvb : VParentBal x.nodes x.values)
    (H : ShaHyp x.nodes x.heads x.values others shaS shaR)
    (hD : DigsBal x.nodes x.heads us) (hDup : DupBal us x.nodes x.values)
    (hEnt : EntBal x.nodes x.values)
    (hheads : ∀ tau,tau≤k.implicitBlks.length → ∃ h∈x.heads,h.tau=tau) :
    witnessPayload (stateWitnessOfV3 k x)≤
      SizeCount.nodePayload x.nodes+SizeCount.valPayload x.values := by
  let reps := (us.filter fun e => e.eq==0).map (fun e => (e.tau,bOf x.nodes x.values e.eid))
  have hcover : ∀ tau,tau≤k.implicitBlks.length → ∀ b∈x.rawStore tau,(tau,b)∈reps := by
    intro tau ht b hbm
    obtain ⟨h,hh,he⟩ := hheads tau ht
    have hcov := store_nondup_coverage hw hhw hvw huw hb hvb H hD hDup hEnt hh
    rw [he] at hcov
    exact hcov b hbm
  have hc := native_witness_payload_le k x reps hcover
  have hr : (reps.map fun p => p.2.length).sum=
      ((us.filter fun e => e.eq==0).map fun e => (bOf x.nodes x.values e.eid).length).sum := by
    simp only [reps,List.map_map,Function.comp_def]
  rw [hr,nondup_payload_exact hw hvw huw hb hvb hD hDup] at hc
  exact hc

end ZkFormal.NearV3.Rcpt.Candidates
