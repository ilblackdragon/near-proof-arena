import ZkFormal.NearV3.Render.Ups.PhysicalNodeTraffic
import ZkFormal.NearV3.Render.Ups.AcceptedTrafficList

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec Assembly ZkFormal.Near ZkFormal.Algebra UpsRows

/-- Physical BYTES sends of one complete serialized node output. -/
def physicalNodeBytes (insts : List UpsInst) (tau k n : Nat) : List Msg :=
  (List.range n).flatMap fun p=>
    uMsgs (fun x=>((cell insts (start insts tau+nodeOffset (inst insts tau) k p) x : Int) : Fp).toNat)
      (fun _=>0) B_BYTES true

private theorem flatMap_eq_map_of {α β : Type} (xs : List α) (f : α→List β) (g : α→β)
    (h : ∀ x∈xs,f x=[g x]) : xs.flatMap f=xs.map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.map_cons,h x (by simp),List.singleton_append]
    rw [ih (fun y hy=>h y (by simp [hy]))]

/-- Complete physical output-node BYTES sends equal the actual native SHA job
preimage in order. Field reductions of identifiers/positions remain explicit. -/
theorem allocated_node_shaBytes {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I →
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I)
    {tau k : Nat} {u : SchedulerUpsertWitness} {I : UpsInst}
    (hu : us[tau]?=some u) (hI : insts[tau]?=some I) (hk : k<nQ I) :
    ∃ M,(upsertShaJobs tau u.value u.run)[k+1]?=some M ∧
      M.id=upsertJobId tau (k+1) ∧ M.bytes=(part I k).q ∧
      physicalNodeBytes insts tau k M.bytes.length=
        (List.range M.bytes.length).map (fun p=>[M.id%P,p%P,M.bytes.getD p 0]) := by
  have ht : tau<insts.length := by
    by_cases ht : tau<insts.length
    · exact ht
    · have hz := List.getElem?_eq_none (Nat.le_of_not_gt ht)
      rw [hz] at hI
      contradiction
  have he : inst insts tau=I := by simp only [inst,List.getD_eq_getElem?_getD,hI,Option.getD_some]
  obtain ⟨ha,hs⟩ := ha tau u I hu hI
  obtain ⟨M,hM,hm,hbytes⟩ := hs.2 k hk
  rw [ha.1] at hM hm
  refine ⟨M,hM,hm,hbytes,?_⟩
  apply flatMap_eq_map_of
  intro p hp
  have hp := List.mem_range.mp hp
  have hpk : p<(part (inst insts tau) k).q.length := by rw [he,←hbytes]; exact hp
  rw [physical_node_bytes ht (he ▸ hk) hpk,he,ha.1,←hbytes]
  have hb : M.bytes.getD p 0<256 := by
    apply (upsertShaJobs_bytes (List.mem_of_getElem? hM)).2
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hp,Option.getD_some]
    exact List.getElem_mem hp
  have hbp : M.bytes.getD p 0<P := by have := P_gt; omega
  rw [Nat.mod_eq_of_lt hbp,hm]
  rfl
end ZkFormal.NearV3.Render.UpsGen
