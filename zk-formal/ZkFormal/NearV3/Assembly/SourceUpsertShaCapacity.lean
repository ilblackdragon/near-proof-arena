import ZkFormal.NearV3.Assembly.UpsertShaCapacity
import ZkFormal.NearV3.Rcpt.Candidates.DedupSha

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Sha.Gen
open Rcpt.Candidates Rcpt.Candidates.DedupCompile

/-- Weights retain whole SHA messages; the source compiler supplies its own
concrete preimages. This list is placement data, not a proof-composition layer. -/
def upsertShaWeights (jobs : List Msg) : List Nat :=
  jobs.map fun M => (msgRows M).length

theorem upsertShaWeights_sum (jobs : List Msg) :
    (upsertShaWeights jobs).sum=(honestRows jobs).length := by
  induction jobs with
  | nil => rfl
  | cons M ms ih => simp only [upsertShaWeights,List.map_cons,List.sum_cons,
      honestRows,List.flatMap_cons,List.length_append] at *; omega

theorem upsertShaWeights_max {jobs : List Msg} (hr : (honestRows jobs).length≤1662140) :
    ∀ a∈upsertShaWeights jobs,a≤1662140 := by
  intro a ha
  have h : ∀ (xs : List Nat), a∈xs → a≤xs.sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons b bs ih =>
      intro hh
      rcases List.mem_cons.mp hh with rfl|hh
      · simp
      · have ht := ih hh; simp only [List.sum_cons]; omega
  have h := h _ ha
  rw [upsertShaWeights_sum] at h
  omega

/-- Actual accepted source and scheduler-upsert message weights fit two log23
partitions without splitting any message. Other SHA kinds remain to be added. -/
theorem checkD0a_source_upsert_partition {cb wb raw : Bytes} {codes : List Bytes}
    {k : WalkD0} {w : StateWitness} {hint : Hint} {p : Prep}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hr : decodeStateWitness raw=.ok w) :
    ∃ us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀u∈us,u.Valid∧u.pre.wf=true) ∧
      let weights := sourceWeights p.lists w.entries ++ upsertShaWeights (schedulerShaJobs 0 us)
      weights.sum≤10594852 ∧
      (splitBudget (2^23) weights).1.sum≤2^23 ∧
      (splitBudget (2^23) weights).2.sum≤2^23 := by
  have hrel := (relD0a_iff B0 cb wb).mpr hc
  obtain ⟨_,_,hs⟩ := relD0a_inputs hrel hp hf hr
  obtain ⟨he,hm⟩ := sourceWeights_exact hr p.lists hs
  have hb := (relD0a_work_bounds hrel hp hf hr).2.1
  obtain ⟨us,hpos,hlen,hvalid,_,_,hrows,_,_⟩ := checkD0a_upsert_sha_capacity hk hw hc
  let weights := sourceWeights p.lists w.entries ++ upsertShaWeights (schedulerShaJobs 0 us)
  have ht : weights.sum≤10594852 := by
    simp only [weights,List.sum_append,upsertShaWeights_sum]
    omega
  have hmax : ∀ a∈weights,a≤1662140 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · have hh := hm a ha; omega
    · exact upsertShaWeights_max hrows a ha
  exact ⟨us,hpos,hlen,hvalid,ht,
    splitBudget_capacity (2^23) 1662140 weights hmax (by decide) (by omega)⟩

end ZkFormal.NearV3.Assembly
