import ZkFormal.NearV3.Render.Ups.RelayFreshSha
namespace ZkFormal.NearV3.Render.UpsRelay
open NearSpec Assembly ZkFormal.Near ZkFormal.Algebra UpsGen

def compactNodeJobs (us : List SchedulerUpsertWitness) : List ZkFormal.Sha.Gen.Msg :=
  (us.mapIdx fun tau u=>(upsertShaJobs tau u.value u.run).tail).flatten

/-- Actual native output SHA jobs have positive slots, hence cannot collide
with any codec fresh-value slot zero. -/
theorem compactNodeJobs_ids {us : List SchedulerUpsertWitness} (hlen : us.length≤32)
    (hp : ∀u∈us,u.run.parts.length≤403) :
    ∀M∈compactNodeJobs us,∃tau j,tau<32 ∧ 1≤j ∧ j<512 ∧ M.id=upsertJobId tau j := by
  intro M hm
  obtain ⟨jobs,hjobs,hm⟩:=List.mem_flatten.mp hm
  obtain ⟨tau,ht,he⟩:=List.mem_iff_getElem.mp hjobs
  simp only [List.length_mapIdx] at ht
  rw [List.getElem_mapIdx] at he
  subst jobs
  change M∈upsertShaFrom tau 1 ((us[tau]).run.parts.map fun p=>NearSpecV3.nodeEnc p.output) at hm
  obtain ⟨j,b,hj,_,hM⟩:=upsertShaFrom_member hm
  have hb:=hp us[tau] (List.getElem_mem ht)
  simp only [List.length_map] at hj
  exact ⟨tau,1+j,by omega,by omega,by omega,by rw [hM]; rfl⟩

/-- No output-node byte is missing from the same checked native inventory. -/
theorem compactGeneratedBytes_nodeJobs {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length)
    (ha : ∀tau u I,us[tau]?=some u → insts[tau]?=some I →
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I) :
    compactGeneratedBytes insts=(compactNodeJobs us).flatMap shaByteMsgs := by
  rw [compactGeneratedBytes_native hl ha]
  simp only [compactNodeJobs,List.flatten_eq_flatMap,List.flatMap_assoc,List.mapIdx_eq_zipIdx_map,List.flatMap_map,Function.comp_def,id]
end ZkFormal.NearV3.Render.UpsRelay
