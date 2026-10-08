import ZkFormal.NearV3.Render.Ups.PhysicalValueTraffic

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec Assembly ZkFormal.Near ZkFormal.Algebra UpsRows

/-- Actual accepted scheduler bytes at their allocated physical rows. No field
reduction remains in the byte, position, or instance-index components. -/
theorem allocated_value_messages {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length) (hn : us.length≤32)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I)
    {tau p : Nat} {u : SchedulerUpsertWitness} {I : UpsInst}
    (hu : us[tau]?=some u) (hI : insts[tau]?=some I) (hp : p<u.value.length)
    (D : URow) (bb : Nat) (sd : Bool) :
    uMsgs (fun x=>((cell insts (start insts tau+(4+p)) x : Int) : Fp).toNat) D bb sd =
      (if B_SPOST=bb ∧ false=sd then [[tau,p,u.value[p].toNat]] else []) ++
      (if B_BYTES=bb ∧ true=sd then [[upsIdN tau 0,p,u.value[p].toNat]] else []) := by
  have ht : tau<insts.length := by
    by_cases ht : tau<insts.length
    · exact ht
    · have hz := List.getElem?_eq_none (Nat.le_of_not_gt ht)
      rw [hz] at hI
      contradiction
  have he : inst insts tau=I := by simp only [inst,List.getD_eq_getElem?_getD,hI,Option.getD_some]
  have hh := ha tau u I hu hI
  have hv := hh.2.2.2.1
  have hlen : L I=u.value.length := by simp only [L,hv,List.length_map]
  have hpI : p<L (inst insts tau) := by rw [he,hlen]; exact hp
  have hvp : I.v.getD p 0=u.value[p].toNat := by
    simp only [hv,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hp,
      Option.map_some,Option.getD_some]
  have htP : tau<P := by have := P_gt; omega
  have hpP : p<P := by
    have hs := hh.2.2.2.2.1.Lsmall
    rw [hlen] at hs
    have : 2^24<P := by decide
    omega
  have hbP : u.value[p].toNat<P := by
    have hb := (u.value[p]).toNat_lt
    have := P_gt
    omega
  have hx := physical_value_messages ht hpI D bb sd
  rw [he,hh.1,hvp,Nat.mod_eq_of_lt htP,Nat.mod_eq_of_lt hpP,Nat.mod_eq_of_lt hbP] at hx
  exact hx

private theorem flatMap_eq_map_of {α β : Type} (xs : List α) (f : α→List β) (g : α→β)
    (h : ∀ x∈xs,f x=[g x]) : xs.flatMap f=xs.map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.map_cons,h x (by simp),List.singleton_append]
    rw [ih (fun y hy=>h y (by simp [hy]))]

/-- Ordered physical fresh-value messages for one allocated instance. -/
def physicalValueMsgs (insts : List UpsInst) (tau n bb : Nat) (sd : Bool) : List Msg :=
  (List.range n).flatMap fun p=>
    uMsgs (fun x=>((cell insts (start insts tau+(4+p)) x : Int) : Fp).toNat) (fun _=>0) bb sd

/-- The complete SPOST receive list is exactly the accepted scheduler value. -/
theorem allocated_value_spost {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length) (hn : us.length≤32)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I)
    {tau : Nat} {u : SchedulerUpsertWitness} {I : UpsInst}
    (hu : us[tau]?=some u) (hI : insts[tau]?=some I) :
    physicalValueMsgs insts tau u.value.length B_SPOST false=
      (List.range u.value.length).map (fun p=>[tau,p,(u.value.getD p 0).toNat]) := by
  apply flatMap_eq_map_of
  intro p hp
  have hp := List.mem_range.mp hp
  rw [allocated_value_messages hl hn ha hu hI hp]
  simp [B_SPOST,B_BYTES,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hp]

/-- The complete fresh-value BYTES send list targets the scheduler SHA job. -/
theorem allocated_value_bytes {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length) (hn : us.length≤32)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I)
    {tau : Nat} {u : SchedulerUpsertWitness} {I : UpsInst}
    (hu : us[tau]?=some u) (hI : insts[tau]?=some I) :
    physicalValueMsgs insts tau u.value.length B_BYTES true=
      (List.range u.value.length).map (fun p=>[upsIdN tau 0,p,(u.value.getD p 0).toNat]) := by
  apply flatMap_eq_map_of
  intro p hp
  have hp := List.mem_range.mp hp
  rw [allocated_value_messages hl hn ha hu hI hp]
  simp [B_SPOST,B_BYTES,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hp]
end ZkFormal.NearV3.Render.UpsGen
