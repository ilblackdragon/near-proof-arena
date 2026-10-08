import ZkFormal.NearV3.Render.Ups.SchedulerExactInstances
import ZkFormal.NearV3.Render.Ups.AcceptedInstanceList
import ZkFormal.NearV3.Render.Ups.AcceptedInstances

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows Assembly ZkFormal.Near

/-- Forgetting the newly retained terminal source ID preserves the old provider API. -/
theorem exactProviders_forget {pairs : List (PTrie×PTrie)} {run : TreeRun} {I : UpsInst}
    (h : ExactNativeWalkProviders pairs run I) : NativeWalkProviders pairs run I := by
  obtain ⟨a,s,hd,hs,hh,hstart,hprefix,hid,hterminal⟩ := h
  exact ⟨a,s,hd,hs,hh,hstart,hprefix,hterminal⟩

/-- A single ordered list realizes all accepted scheduler instances and retains
both byte budgets for the very same operational witnesses. -/
theorem checkD0a_exactNativeTrafficList {cb wb : Bytes} {claim : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok claim) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI) :
    ∃ (us : List SchedulerUpsertWitness) (insts : List UpsInst),
      1≤us.length ∧ us.length≤32 ∧ insts.length=us.length ∧ (∀ u∈us,u.Valid) ∧
      (us.map (fun u=>outputByteCharge u.run)).sum≤2131072 ∧
      (us.map (fun u=>u.value.length)).sum≤3146912 ∧
      ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I ∧
        ExactNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I := by
  classical
  obtain ⟨us,hpos,hlen,hgood,hpre,hout,hval⟩ := checkD0a_upsert_all_bounds hk hw h
  have hex : ∀ i : Fin us.length,∃ I,AllocatedNativeInstance us i us[i] I ∧ NativeShaFamily us[i] I ∧
      ExactNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) (us[i]).run I := by
    intro i
    have hu : us[i.val]?=some us[i] := List.getElem?_eq_getElem i.isLt
    have hget : (us.map SchedulerUpsertWitness.pre)[i.val]?=some (us[i]).pre := by
      simp only [List.getElem?_map,hu,Option.map_some]
    obtain ⟨root,hroot,_⟩ := forestRootAt_exists_of_get 0 0 _ i.val (us[i]).pre hget
    obtain ⟨I,a,b,c,d,e,f,g,h,j⟩ := scheduler_instance_exact_inputs hgood hpre hout hu hroot
      (nativeRootBase (baseI i) (us[i]).pre (us[i]).run) (base i)
    exact ⟨I,⟨a,b,c,d,e,exactProviders_forget f,g,h⟩,j,f⟩
  let insts := List.ofFn (fun i : Fin us.length => Classical.choose (hex i))
  refine ⟨us,insts,hpos,hlen,List.length_ofFn,fun u hu=>(hgood u hu).1,hout,hval,?_⟩
  intro tau u I hu hI
  have ht : tau<us.length := by
    by_cases ht : tau<us.length
    · exact ht
    · have hz := List.getElem?_eq_none (Nat.le_of_not_gt ht)
      rw [hz] at hu
      contradiction
  have hi : I=Classical.choose (hex ⟨tau,ht⟩) := by
    simpa only [insts,List.getElem?_ofFn,dite_eq_left ht,Option.some.injEq] using hI.symm
  have huu : u=us[tau] := (Option.some.inj (hu.symm.trans (List.getElem?_eq_getElem ht)))
  subst I u
  exact Classical.choose_spec (hex ⟨tau,ht⟩)
end ZkFormal.NearV3.Render.UpsGen
