import ZkFormal.NearV3.Render.Ups.WholeByteTraffic

set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec Assembly ZkFormal.Near ZkFormal.Algebra UpsRows

def instanceShaJobs (I : UpsInst) : List ZkFormal.Sha.Gen.Msg :=
  ⟨upsertJobId I.tau 0,I.v,true⟩::
    (List.range (nQ I)).map (fun k=>⟨upsertJobId I.tau (k+1),(part I k).q,true⟩)

/-- Complete job identity, not merely inclusion of each allocated part. -/
theorem instanceShaJobs_native {u : SchedulerUpsertWitness} {I : UpsInst}
    (hv : I.v=u.value.map UInt8.toNat) (hs : NativeShaFamily u I) :
    instanceShaJobs I=upsertShaJobs I.tau u.value u.run := by
  apply List.ext_getElem?
  intro j
  cases j with
  | zero =>
    rw [upsertShaJobs_value]
    simp only [instanceShaJobs,List.getElem?_cons_zero,upsertShaJob,hv]
  | succ k =>
    by_cases hk : k<nQ I
    · obtain ⟨M,hM,hm,hb⟩ := hs.2 k hk
      have hd := (upsertShaJobs_bytes (List.mem_of_getElem? hM)).1
      rw [hM]
      simp only [instanceShaJobs,List.getElem?_cons_succ,List.getElem?_map,
        List.getElem?_range hk,Option.map_some]
      cases M
      simp only at hm hb hd
      cases hm
      cases hb
      cases hd
      rfl
    · have hl : (instanceShaJobs I).length≤k+1 := by simp only [instanceShaJobs,List.length_cons,List.length_map,List.length_range]; omega
      have hr : (upsertShaJobs I.tau u.value u.run).length≤k+1 := by rw [upsertShaJobs_length,←hs.1]; omega
      rw [List.getElem?_eq_none hl,List.getElem?_eq_none hr]

/-- Canonical BYTES messages consumed by a SHA job. -/
def shaByteMsgs (M : ZkFormal.Sha.Gen.Msg) : List Msg :=
  (List.range M.bytes.length).map fun p=>[M.id%P,p%P,(M.bytes.getD p 0)%P]

theorem instance_byteMsgs_jobs (I : UpsInst) :
    valueByteMsgs I++nodeByteMsgs I=(instanceShaJobs I).flatMap shaByteMsgs := by
  simp only [instanceShaJobs,List.flatMap_cons,List.flatMap_map,shaByteMsgs,
    valueByteMsgs,nodeByteMsgs,L,upsIdN,upsertJobId,K_VUPS,Function.comp_def]

/-- All physical rows' byte streams equal the complete SHA job inventory. -/
theorem generatedBytes_jobs (insts : List UpsInst) :
    generatedBytes insts=(List.range insts.length).flatMap
      (fun i=>(instanceShaJobs (inst insts i)).flatMap shaByteMsgs) := by
  rw [generatedBytes_exact]
  simp only [instance_byteMsgs_jobs]

/-- The allocated instance's full byte stream is exactly its actual operational
scheduler SHA inventory, including slot zero and every native output part. -/
theorem allocated_byteMsgs_native {us : List SchedulerUpsertWitness} {tau : Nat}
    {u : SchedulerUpsertWitness} {I : UpsInst}
    (ha : AllocatedNativeInstance us tau u I) (hs : NativeShaFamily u I) :
    valueByteMsgs I++nodeByteMsgs I=(upsertShaJobs tau u.value u.run).flatMap shaByteMsgs := by
  rw [instance_byteMsgs_jobs,instanceShaJobs_native ha.2.2.2.1 hs,ha.1]

/-- Exact whole-table BYTES inventory of all actual accepted scheduler jobs. -/
theorem generatedBytes_native {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I →
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I) :
    generatedBytes insts=(us.mapIdx (fun tau u=>upsertShaJobs tau u.value u.run)).flatMap
      (fun jobs=>jobs.flatMap shaByteMsgs) := by
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
  exact generatedBytes_jobs insts
end ZkFormal.NearV3.Render.UpsGen
