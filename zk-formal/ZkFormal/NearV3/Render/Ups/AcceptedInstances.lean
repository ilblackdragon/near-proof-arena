import ZkFormal.NearV3.Render.Ups.SchedulerInstances
import ZkFormal.NearV3.Assembly.RootedUpsert

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows Assembly ZkFormal.Near

/-- Accepted input produces actual native update instances with authenticated
walk providers and every local part input. Roots and fresh bytes belong to the
same accepted operational executions; global placement and traffic remain separate. -/
theorem checkD0a_nativeInstances {cb wb : Bytes} {claim : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok claim) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI) :
    ∃ us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀ u∈us,u.Valid) ∧
      ∀ tau u,us[tau]?=some u → ∃ I : UpsInst,
        I.tau=tau ∧ I.mid=u.pre.hashOf.map UInt8.toNat ∧ I.post=u.run.output.hashOf.map UInt8.toNat ∧
        I.v=u.value.map UInt8.toNat ∧ InstOk I ∧
        NativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I ∧ NativePartFamily I := by
  obtain ⟨us,hpos,hlen,hgood,hpre,hout,_⟩ := checkD0a_upsert_all_bounds hk hw h
  refine ⟨us,hpos,hlen,fun u hu=>(hgood u hu).1,?_⟩
  intro tau u hu
  have hget : (us.map SchedulerUpsertWitness.pre)[tau]?=some u.pre := by
    simp only [List.getElem?_map,hu,Option.map_some]
  obtain ⟨root,hroot,_⟩ := forestRootAt_exists_of_get 0 0 _ tau u.pre hget
  exact scheduler_instance_inputs hgood hpre hout hu hroot (nativeRootBase (baseI tau) u.pre u.run) (base tau)
end ZkFormal.NearV3.Render.UpsGen
