import ZkFormal.NearV3.Rcpt.Candidates.UniqCount

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near ZkFormal.Algebra NearSpec NearSpecV3 Link3 Assembly

/-- Actual uniqueness/SHA/parent buses cover every retained native record by a
nonduplicate counted representative. No byte-coverage premise remains. -/
theorem native_count_from_uniqueness (k : WalkD0) (x : ExtV3)
    {us : List UniqE} {others : List Msg} {shaS shaR : Nat → List Fp → Nat}
    (hw : NodeWf3 x.nodes) (hhw : HeadWf x.heads) (hvw : ValWf x.values) (huw : UniqWf us)
    (hb : ParentBal x.nodes x.heads) (hvb : VParentBal x.nodes x.values)
    (H : ShaHyp x.nodes x.heads x.values others shaS shaR)
    (hD : DigsBal x.nodes x.heads us) (hDup : DupBal us x.nodes x.values)
    (hEnt : EntBal x.nodes x.values)
    (hheads : ∀ tau,tau≤k.implicitBlks.length → ∃ h∈x.heads,h.tau=tau) :
    witnessRecordCount (stateWitnessOfV3 k x)≤
      (x.nodes.filter (fun s => !s.dup)).length+(x.values.filter (fun e => !e.dup)).length := by
  let reps := (us.filter fun e => e.eq==0).map (fun e => (e.tau,bOf x.nodes x.values e.eid))
  have hcover : ∀ tau,tau≤k.implicitBlks.length → ∀ b∈x.rawStore tau,(tau,b)∈reps := by
    intro tau ht b hbm
    obtain ⟨h,hh,he⟩ := hheads tau ht
    have hcov := store_nondup_coverage hw hhw hvw huw hb hvb H hD hDup hEnt hh
    rw [he] at hcov
    exact hcov b hbm
  have hc := native_witness_count_le k x reps hcover
  have hr : reps.length=(us.filter fun e => e.eq==0).length := List.length_map ..
  rw [hr,nondup_count_exact huw hb hvb hD hDup] at hc
  exact hc

end ZkFormal.NearV3.Rcpt.Candidates
