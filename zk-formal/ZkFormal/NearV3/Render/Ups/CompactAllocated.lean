import ZkFormal.NearV3.Render.Ups.CompactMemory
import ZkFormal.NearV3.Render.Ups.CompactSegmentDigest
import ZkFormal.NearV3.Render.Ups.AllocatedConstraints
namespace ZkFormal.NearV3.Render.UpsRelay
open NearSpec NearSpecV3 Assembly ZkFormal.Near UpsGen
theorem compact_allocated_constraints {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length) (hpos : 1≤us.length)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I)
    (hcap : compactR insts+1≤2^22) {H : Nat} (hH : compactR insts+1≤H) :
    CompactGroupOk insts H compactConstraints := by
  classical
  have hposI : 0<insts.length := by omega
  have hi : ∀I∈insts,InstOk I := fun I hI=>(allocated_local_inputs hl ha hI).1
  have hp : ∀ I∈insts,NativePartFamily I := fun I hI => (allocated_local_inputs hl ha hI).2
  have hf := fun I hI k hk => (hp I hI k hk).2.1
  have hw := fun I hI k hk => (hp I hI k hk).2.2.2.1
  have hm := fun I hI k hk => (hp I hI k hk).2.2.2.2.1
  have hb := fun I hI k hk => Classical.choice (hp I hI k hk).1
  have hplan := fun I hI k hk => (hp I hI k hk).2.2.1
  unfold compactConstraints
  exact compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append
    (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append
    (compact_groupOk_append (compact_cBool hposI hi hH) (compact_cRows hposI hi hH))
    (compact_cConst hposI hi hH)) (compact_cWalk hposI hi hH)) (compact_cSeg hposI hi hH))
    (compact_cPlan hposI hi hplan hH)) (compact_cFields hposI hi hf hw hH))
    (compact_cBytes (by omega) hposI hi hb hH)) (compact_cDigest hposI hi hH)) (compact_cMem hposI hi hf hm hH)

/-- Actual accepted input constructs a compact trace satisfying every candidate
constraint within the unchanged log22 capacity. Global traffic and extraction
are separate obligations; no old UPS capacity is assumed. -/
theorem checkD0a_compact_constraints {cb wb : Bytes} {claim : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok claim) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI) :
    ∃ (us : List SchedulerUpsertWitness) (insts : List UpsInst),
      1≤us.length ∧ us.length≤32 ∧ insts.length=us.length ∧ compactR insts+1≤2^22 ∧
      (∀tau u I,us[tau]?=some u → insts[tau]?=some I →
        AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I) ∧
      CompactGroupOk insts (2^22) compactConstraints := by
  obtain ⟨us,insts,hpos,hlen,hl,hcap,ha⟩:=checkD0a_compact_rows hk hw h baseI base
  exact ⟨us,insts,hpos,hlen,hl,hcap,ha,
    compact_allocated_constraints hl hpos (fun tau u I hu hI=>(ha tau u I hu hI).1) hcap hcap⟩
end ZkFormal.NearV3.Render.UpsRelay
