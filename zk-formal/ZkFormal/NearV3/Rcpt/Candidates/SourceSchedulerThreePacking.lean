import ZkFormal.NearV3.Assembly.SourceSchedulerShaLog22
import ZkFormal.NearV3.Rcpt.Candidates.SourceShaResidualPacking

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Assembly ZkFormal.Sha.Gen DedupCompile

/-- Preallocate the concrete scheduler batch in bin0, then use its residual
capacity for small source messages. No message is split. -/
def schedulerSourceBins (scheduler source : List Nat) : List (List Nat) :=
  let p0 := splitBudget (2^22-scheduler.sum) source
  let p1 := splitBudget (2^22) p0.2
  [scheduler++p0.1,p1.1,p1.2]

theorem schedulerSourceBins_reconstruct (scheduler source : List Nat) :
    (schedulerSourceBins scheduler source).flatten=scheduler++source := by
  have h0 := splitBudget_reconstruct (2^22-scheduler.sum) source
  have h1 := splitBudget_reconstruct (2^22) (splitBudget (2^22-scheduler.sum) source).2
  simp only [schedulerSourceBins,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
  rw [h1,h0]

theorem schedulerSourceBins_fit (scheduler source : List Nat)
    (hsource : source.sum≤8932712) (hmax : ∀ x∈source,x≤35)
    (hsched : scheduler.sum≤1663260) :
    ∀ bin∈schedulerSourceBins scheduler source,bin.sum≤2^22 := by
  obtain ⟨h0,h1,h2⟩ := source_residual_three source scheduler.sum 0 0 hmax (by omega)
    (by decide) (by decide) (by omega)
  intro bin hb
  simp only [schedulerSourceBins,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl
  · simp only [List.sum_append]; omega
  · simpa only [Nat.sub_zero,Nat.add_zero] using h1
  · simpa only [Nat.sub_zero,Nat.add_zero] using h2

/-- Concrete accepted source+upsert+sanity jobs fit THREE whole-message bins.
This is only that subset: prestate/value/receipt/account/Merkle jobs are not
included and no complete3-bin capacity claim follows from this theorem. -/
theorem accepted_source_scheduler_three {cb wb raw : Bytes} {codes : List Bytes}
    {k : WalkD0} {w : StateWitness} {hint : Hint} {p : Prep}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hr : decodeStateWitness raw=.ok w) :
    ∃ us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀u∈us,u.Valid∧u.pre.wf=true) ∧
      let bins := schedulerSourceBins
        (upsertShaWeights (schedulerShaJobs 0 us++schedulerSanityJobs 0 us))
        (sourceWeights p.lists w.entries)
      bins.length=3 ∧
      bins.flatten=upsertShaWeights (schedulerShaJobs 0 us++schedulerSanityJobs 0 us)++
        sourceWeights p.lists w.entries ∧
      (∀ bin∈bins,bin.sum≤2^22) := by
  have hrel := (relD0a_iff B0 cb wb).mpr hc
  obtain ⟨_,_,hs⟩ := relD0a_inputs hrel hp hf hr
  obtain ⟨he,hm⟩ := sourceWeights_exact hr p.lists hs
  have hb := (relD0a_work_bounds hrel hp hf hr).2.1
  obtain ⟨us,hpos,hlen,hvalid,hrows⟩ := checkD0a_scheduler_sha_rows hk hw hc
  refine ⟨us,hpos,hlen,hvalid,rfl,schedulerSourceBins_reconstruct _ _,?_⟩
  apply schedulerSourceBins_fit _ _ (by omega) hm
  rw [upsertShaWeights_sum]
  exact hrows

end ZkFormal.NearV3.Rcpt.Candidates
