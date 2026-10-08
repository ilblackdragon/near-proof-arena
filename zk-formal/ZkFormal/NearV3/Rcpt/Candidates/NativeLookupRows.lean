import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupBranchRows

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

mutual
theorem nativeLookupSteps_rows (nid vid : Nat) : ∀tree key steps,
    tree.wf=true→(∀a∈key,a<16)→nativeLookupSteps nid vid tree key=some steps→lookupRows steps
  | .hash _,_,_,_,_,h=>by cases h
  | .leaf stored slot mem,key,steps,hw,hk,h=>by
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    have hs : ∀a∈stored,a<16 := by simpa [nibblesOk,List.all_eq_true] using hw.1.1.1
    exact leafLookupSteps_rows nid vid slot 0 stored key steps hs hk h
  | .ext stored child mem,key,steps,hw,hk,h=>by
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    have hs : ∀a∈stored,a<16 := by simpa [nibblesOk,List.all_eq_true] using hw.1.1.1
    apply nativeLookup_extension_rows nid vid stored child mem key steps hs hk ?_ h
    intro tail ht
    exact nativeLookupSteps_rows (nid+1) vid child _ tail hw.1.1.2
      (fun a ha=>hk a (List.mem_of_mem_drop ha)) ht
  | .branch value kids mem,[],steps,hw,hk,h=>by
    have hkids : Kids.wf kids 16=true := by
      simp only [PTrie.wf,Bool.and_eq_true] at hw;exact hw.1.2
    exact native_branch_value_rows nid vid value kids mem steps hkids h
  | .branch value kids mem,x::xs,steps,hw,hk,h=>by
    have hkids : Kids.wf kids 16=true := by
      simp only [PTrie.wf,Bool.and_eq_true] at hw;exact hw.1.2
    exact nativeKidsLookupSteps_rows nid (kidsBitmap kids 0) (if value.isSome then 1 else 0) x
      (nid+1) (vid+(optSlotVal value).length) kids 16 x xs steps hkids
      (kidsBitmap_lt kids 16 hkids) (by split <;> decide) (hk x (by simp))
      (fun ha=>native_absent_bitmap kids x ha) (fun a ha=>hk a (by simp [ha])) h

theorem nativeKidsLookupSteps_rows (parent bm hv sym nid vid : Nat) : ∀kids n j key steps,
    Kids.wf kids n=true→bm<2^16→hv≤1→sym<16→
    (nativeChildAt kids j=none→bm/2^sym%2=0)→(∀a∈key,a<16)→
    nativeKidsLookupSteps parent bm hv sym nid vid kids j key=some steps→lookupRows steps
  | .nil,n,j,key,steps,hw,hb,hv',hs,hz,hk,h=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h
    rw [←h]
    exact lookupBranchAbsent_rows parent bm hv sym key hb hv' hs (hz rfl)
  | .none rest,n,0,key,steps,hw,hb,hv',hs,hz,hk,h=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h
    rw [←h]
    exact lookupBranchAbsent_rows parent bm hv sym key hb hv' hs (hz rfl)
  | .some child rest,n,0,key,steps,hw,hb,hv',hs,hz,hk,h=>by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    simp only [nativeKidsLookupSteps] at h
    cases ht : nativeLookupSteps nid vid child key with
    | none=>simp [ht] at h
    | some tail=>
      simp only [ht,Option.map_some,Option.some.injEq] at h
      rw [←h]
      apply lookupRows_prefix [_] tail
      · intro s hm
        simp only [List.mem_singleton] at hm
        subst s
        constructor <;> simp [lookupEdge]
      · exact nativeLookupSteps_rows nid vid child key tail hw.1.2 hk ht
      · have hh:=nativeLookupSteps_length nid vid child key tail ht;omega
  | .none rest,n,j+1,key,steps,hw,hb,hv',hs,hz,hk,h=>by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    exact nativeKidsLookupSteps_rows parent bm hv sym nid vid rest (n-1) j key steps
      hw.2 hb hv' hs hz hk h
  | .some child rest,n,j+1,key,steps,hw,hb,hv',hs,hz,hk,h=>by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    exact nativeKidsLookupSteps_rows parent bm hv sym (nid+tsize child) (vid+(valsOf child).length)
      rest (n-1) j key steps hw.2 hb hv' hs hz hk h
end

theorem nativeLookupSteps_indexed_rows (nid vid : Nat) (tree : PTrie) (key : List Nat)
    (steps : List WStep3) (hw : tree.wf=true) (hk : ∀a∈key,a<16)
    (h : nativeLookupSteps nid vid tree key=some steps) :
    ∀i (hi : i<steps.length),StepOk steps[i] (i+1==steps.length) :=
  lookupRows_indexed steps (nativeLookupSteps_rows nid vid tree key steps hw hk h)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
