import ZkFormal.NearV3.Assembly.SchedulerSanityInput
import ZkFormal.NearV3.Assembly.UpsertShaCapacity

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Sha.Gen

def schedulerWitnessSanity (u : SchedulerUpsertWitness) : Option Bytes :=
  match readKey u.pre keyBwState "bandwidth scheduler state" with
  | .error _ => none
  | .ok prev => (schedPub u.ctx).bind fun pub => schedulerSanityInput pub prev

theorem SchedulerUpsertWitness.sanity {u : SchedulerUpsertWitness} (hv : u.Valid) :
    ∃ input, schedulerWitnessSanity u=some input ∧ input.length=64 ∧
      ∃ links,u.value=(Bandwidth.State.mk links (sha256 input)).encode := by
  obtain ⟨so,hs,hvalue⟩ := hv.2
  obtain ⟨prev,p,o,hread,hpub,hcore,hout,_⟩ := schedStep_complete hs
  obtain ⟨input,hi,hlen,links,hstate⟩ := scheduler_core_sanity hcore (schedPub_hash_length hpub)
  refine ⟨input,?_,hlen,links,?_⟩
  · simp [schedulerWitnessSanity,hread,hpub,hi]
  · rw [←hvalue,←hout]
    exact hstate

def schedulerSanityJob (tau : Nat) (u : SchedulerUpsertWitness) : Msg :=
  ⟨11+16*tau,((schedulerWitnessSanity u).getD []).map UInt8.toNat,true⟩

def schedulerSanityJobs (tau : Nat) : List SchedulerUpsertWitness → List Msg
  | [] => []
  | u::us => schedulerSanityJob tau u::schedulerSanityJobs (tau+1) us

theorem schedulerSanityJob_length (tau : Nat) {u : SchedulerUpsertWitness} (hv : u.Valid) :
    (schedulerSanityJob tau u).bytes.length=64 := by
  obtain ⟨input,hi,hlen,_⟩ := SchedulerUpsertWitness.sanity hv
  simp [schedulerSanityJob,hi,hlen]

theorem schedulerSanityJob_rows (tau : Nat) {u : SchedulerUpsertWitness} (hv : u.Valid) :
    (msgRows (schedulerSanityJob tau u)).length=35 := by
  have hn := ZkFormal.Sha.Complete.nb_eq (schedulerSanityJob tau u)
  rw [schedulerSanityJob_length tau hv] at hn
  rw [sha_message_rows]
  omega

theorem schedulerSanityJobs_rows (tau : Nat) (us : List SchedulerUpsertWitness)
    (hv : ∀u∈us,u.Valid) : (honestRows (schedulerSanityJobs tau us)).length=35*us.length := by
  induction us generalizing tau with
  | nil => rfl
  | cons u us ih =>
    have hh := schedulerSanityJob_rows tau (hv u (by simp))
    have ht := ih (tau+1) (fun x hx => hv x (by simp [hx]))
    simp only [schedulerSanityJobs,honestRows,List.flatMap_cons,List.length_append,
      List.length_cons] at *
    omega

/-- Actual scheduler sanity work adds at most1,120 rows to the concrete upsert
batch; the combined two-kind batch still fits one active log21 table. -/
theorem checkD0a_scheduler_sha_rows {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ()) :
    ∃us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀u∈us,u.Valid∧u.pre.wf=true) ∧
      (honestRows (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us)).length≤1663260 := by
  obtain ⟨us,hpos,hlen,hvalid,_,_,hr,_,_⟩ := checkD0a_upsert_sha_capacity hk hw h
  have hs := schedulerSanityJobs_rows 0 us (fun u hu => (hvalid u hu).1)
  refine ⟨us,hpos,hlen,hvalid,?_⟩
  simp only [honestRows,List.flatMap_append,List.length_append] at *
  omega

end ZkFormal.NearV3.Assembly
