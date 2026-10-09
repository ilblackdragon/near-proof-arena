import ZkFormal.NearV3.Candidates.ProcPreparedSequence
namespace ZkFormal.NearV3.Candidates.ProcPrepBudget
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3 NearSpec

/-- Previous states are indexed by instance position, retaining repeated public
scheduler records rather than identifying them by structural equality. -/
def pairs (p : Prep) (prev : Nat → NearSpec.Bandwidth.State) :=
  p.sched.zipIdx |>.map (fun q=>(q.1,prev q.2))

theorem pairs_length (p : Prep) (prev : Nat → NearSpec.Bandwidth.State) :
    (pairs p prev).length=p.sched.length := by simp [pairs]

theorem pairs_ok {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint=.ok p)
    (prev : Nat → NearSpec.Bandwidth.State) : ∀q∈pairs p prev,SchedPubOk q.1 := by
  intro q hq
  rcases List.mem_map.mp hq with ⟨⟨sp,i⟩,hm,rfl⟩
  apply prepD0_sched h sp
  have hh := List.mem_map.mpr (⟨(sp,i),hm,rfl⟩ : ∃q∈p.sched.zipIdx,Prod.fst q=sp)
  simpa only [List.zipIdx_map_fst] using hh

/-- Actual preparation discharges all process capacity inputs; successful
replay still has to be established from the native scheduler execution. -/
theorem prep_local {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint=.ok p)
    (prev : Nat → NearSpec.Bandwidth.State) (rs : List Run)
    (h : ProcNativeSequence.runInputs (ProcPreparedSequence.inputs (pairs p prev)) 0=.ok rs)
    (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (ProcConcatGeometry.trace rs) t pub :=
  ProcPreparedSequence.prepared_local (pairs p prev) rs
    (by rw [pairs_length]; exact prepD0_len hp) (pairs_ok hp prev) h t pub
end ZkFormal.NearV3.Candidates.ProcPrepBudget
