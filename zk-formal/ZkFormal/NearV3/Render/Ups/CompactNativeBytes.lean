import ZkFormal.NearV3.Render.Ups.CompactByteTraffic
namespace ZkFormal.NearV3.Render.UpsRelay
open NearSpec Assembly ZkFormal.Near ZkFormal.Algebra UpsRows UpsGen

theorem nodeByteMsgs_jobs (I : UpsInst) :
    nodeByteMsgs I=(instanceShaJobs I).tail.flatMap shaByteMsgs := by
  simp only [instanceShaJobs,List.tail_cons,List.flatMap_map,shaByteMsgs,
    nodeByteMsgs,upsIdN,upsertJobId,K_VUPS,Function.comp_def]

theorem compactGeneratedBytes_jobs (insts : List UpsInst) :
    compactGeneratedBytes insts=(List.range insts.length).flatMap
      (fun i=>(instanceShaJobs (inst insts i)).tail.flatMap shaByteMsgs) := by
  rw [compactGeneratedBytes_exact]
  simp only [nodeByteMsgs_jobs]
theorem compactGeneratedBytes_native {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I →
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I) :
    compactGeneratedBytes insts=(us.mapIdx (fun tau u=>upsertShaJobs tau u.value u.run)).flatMap
      (fun jobs=>jobs.tail.flatMap shaByteMsgs) := by
  have hj : (List.range insts.length).map (fun i=>instanceShaJobs (inst insts i))=
      us.mapIdx (fun tau u=>upsertShaJobs tau u.value u.run) := by
    apply List.ext_getElem (by simpa using hl)
    intro i hi hu
    simp only [List.length_map,List.length_range] at hi
    simp only [List.length_mapIdx] at hu
    simp only [List.getElem_map,List.getElem_range,List.getElem_mapIdx]
    have he : inst insts i=insts[i] := by simp only [inst,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    obtain ⟨ha,hs⟩ := ha i us[i] insts[i] (List.getElem?_eq_getElem hu) (List.getElem?_eq_getElem hi)
    rw [he,instanceShaJobs_native ha.2.2.2.1 hs,ha.1]
  rw [←hj,List.flatMap_map]
  exact compactGeneratedBytes_jobs insts
/-- The codec's slot-zero bytes together with compact output bytes retain the
same complete native SHA inventory, instance by instance. -/
theorem relay_and_compact_instance {us : List SchedulerUpsertWitness} {tau : Nat}
    {u : SchedulerUpsertWitness} {I : UpsInst}
    (ha : AllocatedNativeInstance us tau u I) (hs : NativeShaFamily u I) :
    valueByteMsgs I++nodeByteMsgs I=(upsertShaJobs tau u.value u.run).flatMap shaByteMsgs := by
  exact allocated_byteMsgs_native ha hs
end ZkFormal.NearV3.Render.UpsRelay
