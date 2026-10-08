import ZkFormal.NearV3.Assembly.SchedulerInstanceMessages

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Near

private theorem jobs_indexed (start : Nat) (us : List SchedulerUpsertWitness) :
    Sha.Gen.expectedDigests (schedulerShaJobs start us)=
      (List.range us.length).flatMap (fun i=>us[i]?.toList.flatMap (fun u=>
        Sha.Gen.expectedDigests (upsertShaJobs (start+i) u.value u.run))) := by
  induction us generalizing start with
  | nil=>rfl
  | cons u us ih=>
    simp only [schedulerShaJobs,Sha.Gen.expectedDigests,List.filter_append,List.map_append]
    change Sha.Gen.expectedDigests (upsertShaJobs start u.value u.run)++
      Sha.Gen.expectedDigests (schedulerShaJobs (start+1) us)=_
    rw [ih]
    simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.toList_some,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,Nat.add_zero]
    congr 1
    apply congrArg (fun f=>(List.range us.length).flatMap f)
    funext i
    simp only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    rfl

private theorem flat_perm {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,(f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil=>exact List.Perm.refl []
  | cons x xs ih=>
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih (fun y hy=>h y (by simp [hy])))

/-- Every physical compact UPS digest consumer is supplied by exactly the
corresponding accepted scheduler batch, without dropping repeated messages. -/
theorem scheduler_compact_digest_conservation (us : List SchedulerUpsertWitness) (insts : List UpsInst)
    (hlen : insts.length=us.length)
    (hvalid : ∀u∈us,u.Valid ∧ u.pre.wf=true)
    (hinst : ∀i u I,us[i]?=some u→insts[i]?=some I→
      AllocatedNativeInstance us i u I ∧ NativeShaFamily u I ∧ NativeEncodedInstance u I) :
    ((CompactPhysicalDigests.compactGeneratedDigests insts).map Msg.toFp).Perm
      ((Sha.Gen.expectedDigests (schedulerShaJobs 0 us)).map Msg.toFp) := by
  rw [CompactPhysicalDigests.compactGeneratedDigests_windows,List.map_flatMap,jobs_indexed,List.map_flatMap,hlen]
  apply flat_perm
  intro i hi
  have hu:i<us.length:=List.mem_range.mp hi
  have hI:i<insts.length:=by omega
  let u:=us[i]'hu
  let I:=insts[i]'hI
  have hgu:us[i]?=some u:=List.getElem?_eq_getElem hu
  have hgI:insts[i]?=some I:=List.getElem?_eq_getElem hI
  obtain ⟨ha,hs,he⟩:=hinst i u I hgu hgI
  obtain ⟨hv,hw⟩:=hvalid u (List.mem_of_getElem? hgu)
  have hins:inst insts i=I:=by simp [inst,List.getD_eq_getElem?_getD,hgI]
  rw [hgu,hins]
  simp only [Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil,Nat.zero_add]
  rw [←ha.1]
  exact allocated_instance_messages hv hw ha hs he ha.2.2.2.2.1 ha.2.2.2.2.2.2.2

/-- Actual log22 physical DIGEST counter equality for the same installed instances. -/
theorem scheduler_compact_digest_count (us : List SchedulerUpsertWitness) (insts : List UpsInst)
    (hlen : insts.length=us.length)
    (hvalid : ∀u∈us,u.Valid ∧ u.pre.wf=true)
    (hinst : ∀i u I,us[i]?=some u→insts[i]?=some I→
      AllocatedNativeInstance us i u I ∧ NativeShaFamily u I ∧ NativeEncodedInstance u I)
    (hR : UpsRelay.compactR insts≤2^22) (t : Nat) (pub msg : List ZkFormal.Algebra.Fp) :
    tableBusCount UpsRelay.compactTable.interactions (Candidates.CompactHeight.trace insts) t pub B_DIGEST false msg=
      ((Sha.Gen.expectedDigests (schedulerShaJobs 0 us)).map Msg.toFp).count msg := by
  rw [CompactPhysicalDigests.digests insts hR t pub msg]
  exact (scheduler_compact_digest_conservation us insts hlen hvalid hinst).count_eq msg

end ZkFormal.NearV3.Assembly
