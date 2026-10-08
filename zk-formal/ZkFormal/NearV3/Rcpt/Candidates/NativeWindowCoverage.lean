import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderOriginProvider
import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowGeneratedAddress
import ZkFormal.NearV3.Rcpt.Candidates.ChosenReaderOrigins

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows Assembly

/-- Source ownership of every physical compact UPS read, using the same chosen
native runs, encoded instances, and original updated provider forest. -/
theorem native_window_coverage (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (hbudget : preBytes (rs.map ReplayTree.post)≤2000000)
    (us : List SchedulerUpsertWitness) (insts : List UpsInst)
    (hforest : us.map SchedulerUpsertWitness.pre=rs.map ReplayTree.post)
    (hgood : ∀u∈us,u.Valid ∧ u.pre.wf=true)
    (hlen : insts.length=us.length)
    (halloc : ∀tau u I,us[tau]?=some u→insts[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧
      ∃root,forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
        NativeReaderOrigin root u.run u.value I)
    (t r : Nat) (hr : (Candidates.CompactHeight.trace insts).cell t r UpsV3.rd=1) :
    ∃key,key∈nodeWindowKeys
      (records (forestOldInputs rs) (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))) ∧
      windowFieldKey (Candidates.CompactHeight.trace insts) t r=key.map Fp.ofNat := by
  have hex : ∀i,i<insts.length→∃u root,
      us[i]?=some u ∧
      AllocatedNativeInstance us i u (inst insts i) ∧
      forestRootAt 0 0 (rs.map ReplayTree.post) i=some root ∧
      NativeReaderOrigin root u.run u.value (inst insts i) ∧
      traceUpsert root.tree [0,15] u.value=some u.run ∧ root.tree.wf=true := by
    intro i hi
    have hui : i<us.length := hlen ▸ hi
    have hu : us[i]?=some us[i] := List.getElem?_eq_getElem hui
    have hI : insts[i]?=some (inst insts i) := by
      simp [inst,List.getElem?_eq_getElem hi]
    obtain ⟨a,root,hroot,ho⟩:=halloc i _ _ hu hI
    have ht:=forestRootAt_tree 0 0 (us.map SchedulerUpsertWitness.pre) i
    rw [hroot,List.getElem?_map,hu] at ht
    have heq : root.tree=(us[i]).pre := Option.some.inj ht
    obtain ⟨hv',hw'⟩:=hgood _ (List.getElem_mem hui)
    refine ⟨_,root,hu,a,hforest ▸ hroot,ho,?_,heq ▸ hw'⟩
    simpa only [heq,keyBwState_nibbles] using hv'.1
  have hi : ∀I∈insts,InstOk I ∧ NativePartFamily I := by
    intro I hI
    obtain ⟨i,hi,hget⟩:=List.mem_iff_getElem.mp hI
    obtain ⟨u,root,hu,a,_⟩:=hex i hi
    have he : inst insts i=I := by simp [inst,List.getElem?_eq_getElem hi,hget]
    rw [←he]
    exact ⟨a.2.2.2.2.1,a.2.2.2.2.2.2.2⟩
  have hroom : ∀I∈insts,∀k,k<nQ I→(part I k).phk+9≤(part I k).pb.length := by
    intro I hI k hk
    obtain ⟨i,hi,hget⟩:=List.mem_iff_getElem.mp hI
    obtain ⟨u,root,hu,a,hroot,ho,hr',hw'⟩:=hex i hi
    have he : inst insts i=I := by simp [inst,List.getElem?_eq_getElem hi,hget]
    rw [←he] at hk ⊢
    exact ho.room hr' hw' k hk
  obtain ⟨i,k,p,pos,hi',hk,hp,hkind,hpos,hkey⟩:=compact_read_address insts hi hroom t r hr
  obtain ⟨u,root,hu,a,hroot,ho,hr',hw'⟩:=hex i hi'
  exact ⟨_,ho.provider rs hv hw hbudget hroot hr' k pos hk hkind hpos,hkey⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
