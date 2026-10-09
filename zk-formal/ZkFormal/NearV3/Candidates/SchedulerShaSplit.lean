import ZkFormal.NearV3.Candidates.CompactPhysicalShaBytes
import ZkFormal.NearV3.Assembly.UpsertShaCapacity

namespace ZkFormal.NearV3.Candidates.SchedulerShaSplit
open ZkFormal.NearV3.Assembly ZkFormal.NearV3.Render.UpsGen ZkFormal.NearV3.Render.UpsRelay

def freshJobs : Nat→List SchedulerUpsertWitness→List Sha.Gen.Msg
  | _,[] => []
  | tau,u::us => upsertShaJob tau 0 u.value::freshJobs (tau+1) us

def nodeJobs : Nat→List SchedulerUpsertWitness→List Sha.Gen.Msg
  | _,[] => []
  | tau,u::us => (upsertShaJobs tau u.value u.run).tail++nodeJobs (tau+1) us

/-- Whole native SHA jobs split by their actual physical producer, retaining
all identifiers, payload bytes and multiplicities. -/
theorem partition (tau : Nat) (us : List SchedulerUpsertWitness) :
    (schedulerShaJobs tau us).Perm (freshJobs tau us++nodeJobs tau us) := by
  induction us generalizing tau with
  | nil => exact List.Perm.refl []
  | cons u us ih =>
    change (upsertShaJob tau 0 u.value::
      ((upsertShaJobs tau u.value u.run).tail++schedulerShaJobs (tau+1) us)).Perm
      (upsertShaJob tau 0 u.value::
        (freshJobs (tau+1) us++((upsertShaJobs tau u.value u.run).tail++nodeJobs (tau+1) us)))
    apply List.Perm.cons
    have h:=(ih (tau+1)).append_left (upsertShaJobs tau u.value u.run).tail
    have hs:=(List.perm_append_comm (l₁:=(upsertShaJobs tau u.value u.run).tail)
      (l₂:=freshJobs (tau+1) us)).append_right (nodeJobs (tau+1) us)
    exact h.trans (by simpa only [List.append_assoc] using hs)

theorem nodes_mapIdx (tau : Nat) (us : List SchedulerUpsertWitness) :
    nodeJobs tau us=(us.mapIdx fun i u=>(upsertShaJobs (tau+i) u.value u.run).tail).flatten := by
  induction us generalizing tau with
  | nil => rfl
  | cons u us ih =>
    simp only [nodeJobs,List.mapIdx_cons,Nat.add_zero,List.flatten_cons,ih]
    congr 2
    congr 1
    funext i u
    rw [show tau+1+i=tau+(i+1) by omega]

theorem nodes (us : List SchedulerUpsertWitness) : nodeJobs 0 us=compactNodeJobs us := by
  simpa only [compactNodeJobs,Nat.zero_add] using nodes_mapIdx 0 us

theorem fresh_mapIdx (tau : Nat) (us : List SchedulerUpsertWitness) :
    freshJobs tau us=us.mapIdx (fun i u=>upsertShaJob (tau+i) 0 u.value) := by
  induction us generalizing tau with
  | nil => rfl
  | cons u us ih =>
    simp only [freshJobs,List.mapIdx_cons,Nat.add_zero,ih]
    congr 2
    funext i u
    rw [show tau+1+i=tau+(i+1) by omega]

/-- The remaining slot-zero jobs are exactly the native fresh-value bytes that
the codec relay must send, with global transition indices preserved. -/
theorem fresh_bytes (tau : Nat) (us : List SchedulerUpsertWitness) :
    Sha.Gen.expectedBytes (freshJobs tau us)=
      (us.mapIdx fun i u=>relayValueMsgs (tau+i) u.value).flatten := by
  simp only [fresh_mapIdx,Sha.Gen.expectedBytes,List.mapIdx_eq_zipIdx_map,
    List.flatMap_map,List.flatten_eq_flatMap,relayValueMsgs,
    upsertShaJob,List.length_map]
  rfl

end ZkFormal.NearV3.Candidates.SchedulerShaSplit
