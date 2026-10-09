import ZkFormal.NearV3.Render.Ups.AllocatedRowCost
import ZkFormal.NearV3.Render.Ups.GSeg
import ZkFormal.NearV3.Render.Ups.GDig
import ZkFormal.NearV3.Render.Ups.GWalk
import ZkFormal.NearV3.Render.Ups.GRows
import ZkFormal.NearV3.Render.Ups.GBool
import ZkFormal.NearV3.Render.Ups.GPlan
import ZkFormal.NearV3.Render.Ups.GFieldsComplete
import ZkFormal.NearV3.Render.Ups.GMem
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 Assembly ZkFormal.Near

/-- Membership in the ordered allocation supplies all local instance semantics. -/
theorem allocated_local_inputs {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I)
    {I : UpsInst} (hI : I∈insts) : InstOk I ∧ NativePartFamily I := by
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hI
  have hu : k<us.length := hl ▸ hk
  have hp := ha k us[k] insts[k] (List.getElem?_eq_getElem hu) (List.getElem?_eq_getElem hk)
  exact ⟨hp.2.2.2.2.1,hp.2.2.2.2.2.2.2⟩

/-- The only additional honest-input obligation is the actual physical row cap. -/
theorem allocated_upsOk {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length) (hpos : 1≤us.length)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I)
    (hcap : R insts+1≤2^22) : UpsOk insts :=
  ⟨by omega,fun I hI=>(allocated_local_inputs hl ha hI).1,hcap⟩

/-- Every UPS polynomial is discharged from actual allocated native instances.
The fixed row capacity remains explicit; no AIR equation is an input premise. -/
theorem allocated_constraints {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length) (hpos : 1≤us.length)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I)
    (hcap : R insts+1≤2^22) {H : Nat} (hH : R insts+1≤H) :
    GroupOk insts H UpsV3.constraints := by
  classical
  have ok := allocated_upsOk hl hpos ha hcap
  have hp : ∀ I∈insts,NativePartFamily I := fun I hI => (allocated_local_inputs hl ha hI).2
  have hf := fun I hI k hk => (hp I hI k hk).2.1
  have hw := fun I hI k hk => (hp I hI k hk).2.2.2.1
  have hm := fun I hI k hk => (hp I hI k hk).2.2.2.2.1
  have hb := fun I hI k hk => Classical.choice (hp I hI k hk).1
  have hplan := fun I hI k hk => (hp I hI k hk).2.2.1
  unfold UpsV3.constraints
  exact groupOk_append (groupOk_append (groupOk_append (groupOk_append
    (groupOk_append (groupOk_append (groupOk_append (groupOk_append
    (groupOk_append (cBool_ok ok hH) (cRows_ok ok hH))
    (cConst_ok ok hH)) (cWalk_ok ok hH)) (cSeg_ok ok hH))
    (cPlan_ok ok hplan hH)) (cFields_ok ok hf hw hH))
    (cBytes_ok ok hb hH)) (cDigest_ok ok hH)) (cMem_ok ok hf hm hH)
/-- Accepted input yields the complete ordered local UPS trace. This exposes
capacity as the remaining obligation, rather than silently strengthening acceptance. -/
theorem checkD0a_allocated_constraints {cb wb : Bytes} {claim : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok claim) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI) :
    ∃ (us : List SchedulerUpsertWitness) (insts : List UpsInst),
      1≤us.length ∧ us.length≤32 ∧ insts.length=us.length ∧
      insts.map UpsInst.tau=List.range us.length ∧ R insts≤5278112 ∧
      (∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I) ∧
      (R insts+1≤2^22 → GroupOk insts (2^22) UpsV3.constraints) := by
  obtain ⟨us,insts,hpos,hlen,hl,_,hout,hval,ha⟩ := checkD0a_nativeInstanceList hk hw h baseI base
  exact ⟨us,insts,hpos,hlen,hl,allocated_taus hl ha,
    allocated_rows_bound hl ha hlen hval hout,ha,
    fun hc=>allocated_constraints hl hpos ha hc hc⟩
end ZkFormal.NearV3.Render.UpsGen
