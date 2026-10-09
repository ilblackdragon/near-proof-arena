import ZkFormal.NearV3.Rcpt.Candidates.NativeWindowCoverage
import ZkFormal.NearV3.Candidates.WindowKeyCanonical

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Render Render.UpsGen Render.UpsRelay UpsRows Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Canonical provider fields convert the mapped ownership already derived
from native construction into the natural ownership required for counter balance. -/
theorem physical_window_owner {vs : List NodeS3} (hw : NodeWf3 vs)
    (hb : ∀s∈vs,∀x∈s.v.ser true,x<256)
    (tr : Trace Fp) (t r : Nat) {key : Msg} (hk : key∈nodeWindowKeys vs)
    (he : windowFieldKey tr t r=key.map Fp.ofNat) :
    physicalWindowKey tr t r∈nodeWindowKeys vs := by
  obtain ⟨⟨s,n⟩,hs,hk'⟩:=List.mem_flatMap.mp hk
  obtain ⟨p,hp,hkey⟩:=List.mem_map.mp hk'
  obtain ⟨i,hi,hget⟩:=List.mem_iff_getElem.mp hs
  have hil : i<vs.length := by simpa using hi
  have hg : vs[i]=s ∧ i=n := by
    simpa only [List.getElem_zip,List.getElem_range,Prod.mk.injEq] using hget
  obtain ⟨hgs,rfl⟩:=hg
  have hsn : vs[i]?=some s := List.getElem?_eq_some_iff.mpr ⟨hil,hgs⟩
  have hs_mem:=List.mem_of_getElem? hsn
  have hp' := List.mem_range.mp hp
  have he' : windowFieldKey tr t r=(windowKey i p s).map Fp.ofNat := by rw [hkey];exact he
  rw [Candidates.WindowKeyCanonical.physical_eq hw hsn hp' (hb s hs_mem) tr t r he']
  exact nodeWindowKeys_mem hsn hp'

theorem native_physical_window_coverage (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (hbudget : preBytes (rs.map ReplayTree.post)≤2000000)
    (us : List SchedulerUpsertWitness) (insts : List UpsInst)
    (hforest : us.map SchedulerUpsertWitness.pre=rs.map ReplayTree.post)
    (hgood : ∀u∈us,u.Valid ∧ u.pre.wf=true)
    (hlen : insts.length=us.length)
    (halloc : ∀tau u I,us[tau]?=some u→insts[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧
      ∃root,forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
        NativeReaderOrigin root u.run u.value I)
    (hn : NodeWf3 (records (forestOldInputs rs)
      (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))))
    (hb : ∀s∈records (forestOldInputs rs)
      (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre))),∀x∈s.v.ser true,x<256)
    (t : Nat) : ∀r∈physicalWindowRows (Candidates.CompactHeight.trace insts) t,
      physicalWindowKey (Candidates.CompactHeight.trace insts) t r∈nodeWindowKeys
        (records (forestOldInputs rs) (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))) := by
  intro r hr
  have hrd : (Candidates.CompactHeight.trace insts).cell t r UpsV3.rd=1 := by
    simpa only [physicalWindowRows,List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp hr).2
  obtain ⟨key,hkey,he⟩:=native_window_coverage rs hv hw hbudget us insts hforest hgood hlen halloc t r hrd
  exact physical_window_owner hn hb _ t r hkey he

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
