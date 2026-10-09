import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderRankAllocated

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

theorem rankUpsList_length (p : List WStep3) (Is : List UpsInst) :
    (rankUpsList p Is).length=Is.length := by
  induction Is generalizing p with
  | nil => rfl
  | cons I Is ih => simp [rankUpsList,ih]

theorem rankUpsList_get : ∀(Is : List UpsInst)(p : List WStep3)(i : Nat)(J : UpsInst),
    (rankUpsList p Is)[i]?=some J→∃I q,Is[i]?=some I ∧ J=rankUps q I
  | [],_,_,_,h=>by simp [rankUpsList] at h
  | I::Is,p,0,J,h=>by
    simp only [rankUpsList,List.getElem?_cons_zero,Option.some.injEq] at h
    exact ⟨I,p,rfl,h.symm⟩
  | I::Is,p,i+1,J,h=>by
    simp only [rankUpsList,List.getElem?_cons_succ] at h
    exact rankUpsList_get Is (p++fourSteps I) i J h

theorem physicalPrefixUps_get (p : List WStep3) (Is : List UpsInst) (i : Nat) (J : UpsInst)
    (h : (physicalPrefixUps p Is)[i]?=some J) :
    ∃I q,Is[i]?=some I ∧ J=syncUps (rankUps q I) := by
  obtain ⟨K,hK,rfl⟩ : ∃K,(rankUpsList p Is)[i]?=some K ∧ syncUps K=J := by
    simpa only [physicalPrefixUps,List.getElem?_map,Option.map_eq_some_iff] using h
  obtain ⟨I,q,hI,rfl⟩:=rankUpsList_get Is p i K hK
  exact ⟨I,q,hI,rfl⟩

/-- The same globally indexed native runs retain their encoded-source origin
when the shared prefix consumer inventory assigns EDGE/BMAP counters. -/
theorem physicalPrefixUps_origins {us : List SchedulerUpsertWitness} {Is : List UpsInst}
    (h : ∀tau u I,us[tau]?=some u→Is[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I ∧
      ∃root,forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
        NativeReaderOrigin root u.run u.value I)
    (p : List WStep3) :
    (physicalPrefixUps p Is).length=Is.length ∧
    ∀tau u J,us[tau]?=some u→(physicalPrefixUps p Is)[tau]?=some J→
      AllocatedNativeInstance us tau u J ∧ NativeShaFamily u J ∧
      ∃root,forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
        NativeReaderOrigin root u.run u.value J := by
  refine ⟨by simp [physicalPrefixUps,rankUpsList_length],?_⟩
  intro tau u J hu hJ
  obtain ⟨I,q,hI,rfl⟩:=physicalPrefixUps_get p Is tau J hJ
  obtain ⟨ha,hs,root,hroot,ho⟩:=h tau u I hu hI
  exact ⟨ranked_native_allocation ha q,ranked_native_sha hs q,root,hroot,ho.ranked q⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
