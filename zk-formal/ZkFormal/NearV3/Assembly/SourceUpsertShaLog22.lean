import ZkFormal.NearV3.Assembly.SourceUpsertShaCapacity

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Sha.Gen
open Rcpt.Candidates Rcpt.Candidates.DedupCompile

/-- A nonempty remainder starts with the whole message that did not fit. -/
theorem splitBudget_remainder_cost (cap maxMessage : Nat) (xs : List Nat)
    (hm : ∀ a∈xs,a≤maxMessage) (hn : (splitBudget cap xs).2≠[]) :
    (splitBudget cap xs).2.sum+cap≤xs.sum+maxMessage := by
  have hj := splitBudget_reconstruct cap xs
  have he := congrArg List.sum hj
  simp only [List.sum_append] at he
  cases hr : (splitBudget cap xs).2 with
  | nil => exact False.elim (hn hr)
  | cons a rest =>
    have hs := splitBudget_stop cap xs hr
    have ha : a∈xs := by rw [←hj,hr]; simp
    have hh := hm a ha
    rw [hr] at he
    omega

def sourceShaBins (weights : List Nat) : List (List Nat) :=
  let p := splitBudget (2^22) weights
  let q := splitBudget (2^22) p.2
  [p.1,q.1,q.2]

theorem sourceShaBins_reconstruct (weights : List Nat) :
    (sourceShaBins weights).flatten=weights := by
  simp only [sourceShaBins,List.flatten_cons,List.flatten_nil,List.append_nil]
  rw [splitBudget_reconstruct,splitBudget_reconstruct]

theorem sourceShaBins_fit (weights : List Nat)
    (hm : ∀ a∈weights,a≤35) (ht : weights.sum≤8932712) :
    ∀ bin∈sourceShaBins weights,bin.sum≤2^22 := by
  let p := splitBudget (2^22) weights
  have hj := splitBudget_reconstruct (2^22) weights
  have hm' : ∀ a∈p.2,a≤35 := by
    intro a ha
    apply hm
    rw [←hj]
    exact List.mem_append_right _ ha
  have ht' : p.2.sum≤4738443 := by
    by_cases hn : p.2=[]
    · simp [hn]
    · have hh := splitBudget_remainder_cost (2^22) 35 weights hm hn; change p.2.sum+_≤_ at hh; omega
  have hq := splitBudget_capacity (2^22) 35 p.2 hm' (by decide) (by omega)
  intro bin hb
  simp only [sourceShaBins,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl
  · exact splitBudget_prefix_le _ _
  · exact hq.1
  · exact hq.2

/-- Uses the existing active log22 SHA cap: three whole-message source bins and
one upsert bin. This establishes placement, not physical routing or ownership. -/
theorem checkD0a_source_upsert_log22 {cb wb raw : Bytes} {codes : List Bytes}
    {k : WalkD0} {w : StateWitness} {hint : Hint} {p : Prep}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hr : decodeStateWitness raw=.ok w) :
    ∃ us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀u∈us,u.Valid∧u.pre.wf=true) ∧
      let bins := sourceShaBins (sourceWeights p.lists w.entries) ++
        [upsertShaWeights (schedulerShaJobs 0 us)]
      bins.length=4 ∧
      bins.flatten=sourceWeights p.lists w.entries ++ upsertShaWeights (schedulerShaJobs 0 us) ∧
      (∀ bin∈bins,bin.sum≤2^22) := by
  have hrel := (relD0a_iff B0 cb wb).mpr hc
  obtain ⟨_,_,hs⟩ := relD0a_inputs hrel hp hf hr
  obtain ⟨he,hm⟩ := sourceWeights_exact hr p.lists hs
  have hb := (relD0a_work_bounds hrel hp hf hr).2.1
  obtain ⟨us,hpos,hlen,hvalid,_,_,hrows,_,_⟩ := checkD0a_upsert_sha_capacity hk hw hc
  refine ⟨us,hpos,hlen,hvalid,by simp [sourceShaBins],?_,?_⟩
  · simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
      sourceShaBins_reconstruct]
  · intro bin hbin
    rcases List.mem_append.mp hbin with hbin|hbin
    · exact sourceShaBins_fit _ hm (by omega) bin hbin
    · simp only [List.mem_singleton] at hbin
      subst bin
      rw [upsertShaWeights_sum]
      omega

end ZkFormal.NearV3.Assembly
