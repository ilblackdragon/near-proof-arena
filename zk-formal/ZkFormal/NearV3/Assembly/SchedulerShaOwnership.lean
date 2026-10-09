import ZkFormal.NearV3.Assembly.SchedulerAllBounds
import ZkFormal.NearV3.Assembly.SchedulerSanityJobs

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen ZkFormal.Sha.Gen

theorem schedulerShaJobs_ids (tau : Nat) (us : List SchedulerUpsertWitness)
    (ht : tau+us.length≤32) (hp : ∀u∈us,u.run.parts.length≤403) :
    ∀M∈schedulerShaJobs tau us,M.id<ZkFormal.Algebra.P ∧ M.id%16=12 := by
  induction us generalizing tau with
  | nil => simp [schedulerShaJobs]
  | cons u us ih =>
    intro M hm
    rcases List.mem_append.mp hm with hm|hm
    · have hu := hp u (by simp)
      obtain ⟨i,b,hi,_,rfl⟩ := upsertShaFrom_member hm
      simp only [List.length_cons,List.length_map] at hi ht
      have hid := upsertJobId_bound (by omega : tau<32) (by omega : 0+i<512)
      have hk := upsertJobId_kind tau (0+i)
      change upsertJobId tau (0+i)<ZkFormal.Algebra.P ∧ upsertJobId tau (0+i)%16=12
      refine ⟨Nat.lt_trans hid (by decide),hk⟩
    · exact ih (tau+1) (by simp only [List.length_cons] at ht;omega)
        (fun x hx=>hp x (by simp [hx])) M hm

theorem schedulerSanityJobs_ids (tau : Nat) (us : List SchedulerUpsertWitness)
    (ht : tau+us.length≤32) :
    ∀M∈schedulerSanityJobs tau us,M.id<ZkFormal.Algebra.P ∧ M.id%16=11 := by
  induction us generalizing tau with
  | nil => simp [schedulerSanityJobs]
  | cons u us ih =>
    intro M hm
    rcases List.mem_cons.mp hm with rfl|hm
    · simp only [schedulerSanityJob,ZkFormal.Algebra.P]
      simp only [List.length_cons] at ht
      constructor <;> omega
    · exact ih (tau+1) (by simp only [List.length_cons] at ht;omega) M hm

/-- Canonical IDs of the actual scheduler jobs occupy exactly the disjoint
kind11 and kind12 registry slots; no field-wrap alias with trie/source kinds. -/
theorem checkD0a_scheduler_sha_ids {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ()) :
    ∃us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀u∈us,u.Valid∧u.pre.wf=true) ∧
      ∀M∈schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us,
        M.id<ZkFormal.Algebra.P ∧ (M.id%16=11 ∨ M.id%16=12) := by
  obtain ⟨us,hpos,hlen,hvalid,_,_,_⟩ := checkD0a_upsert_all_bounds hk hw hc
  refine ⟨us,hpos,hlen,fun u hu=>⟨(hvalid u hu).1,(hvalid u hu).2.1⟩,?_⟩
  intro M hm
  rcases List.mem_append.mp hm with hm|hm
  · obtain ⟨hb,hk⟩ := schedulerShaJobs_ids 0 us (by omega) (fun u hu=>(hvalid u hu).2.2.1) M hm
    exact ⟨hb,Or.inr hk⟩
  · obtain ⟨hb,hk⟩ := schedulerSanityJobs_ids 0 us (by omega) M hm
    exact ⟨hb,Or.inl hk⟩

end ZkFormal.NearV3.Assembly
