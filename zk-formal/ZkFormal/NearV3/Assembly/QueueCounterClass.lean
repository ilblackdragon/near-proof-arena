import ZkFormal.NearV3.Assembly.QueueProviderModes

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv Qv.Candidates.CombinedWalkGen

theorem queueRankResolve_selected_iff {pre : PTrie} {rs : List ReadRequest} {slot : Nat}
    {r : ReadRequest} (hr : rs[slot]?=some r) (hh : r.Holds pre) (base i : Nat) :
    (r.value.isSome=true ∧ (queueRankResolve pre rs base slot).1=base+i) ↔
      valueIndex pre r.key=some i := by
  cases hi : valueIndex pre r.key with
  | none =>
    have hv : r.value.isSome=false := by
      cases hv : r.value with
      | none => rfl
      | some b =>
        have hf := hh.1
        rw [hv] at hf
        obtain ⟨j,hj,_⟩ := valueIndex_complete pre r.key b hf
        simp [hi] at hj
    simp [hv]
  | some j =>
    obtain ⟨b,hb⟩ := valueIndex_defined pre r.key j hi
    have hv : r.value=some b := Option.some.inj (hh.1.symm.trans hb)
    rw [queueRankResolve_present hr hi base]
    simp [hv]

private theorem filterMap_congr_mem {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ x ∈ xs, f x=g x) : xs.filterMap f=xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    rw [h x (by simp),ih (fun y hy => h y (by simp [hy]))]

/-- The actual present/vid class in generated main walks has consecutive ranks. -/
theorem mainPlan_counter_class (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (hh : ∀ r ∈ mainRequests pre v, r.Holds pre) (i : Nat) :
    (mainPlan pre v pres.length (queueForestRankResolve (queueInputs pre v pres) 0)).filterMap
      (fun w => if w.value.isSome && w.vid==i then some w.users else none) =
      List.range' 0 (queueUsers pre (mainRequests pre v) i) := by
  have he : (mainPlan pre v pres.length (queueForestRankResolve (queueInputs pre v pres) 0)).filterMap
      (fun w => if w.value.isSome && w.vid==i then some w.users else none) =
    (mainPlan pre v pres.length (queueForestRankResolve (queueInputs pre v pres) 0)).filterMap
      (fun w => if valueIndex pre (w.request v.shards).key==some i then some w.users else none) := by
    apply filterMap_congr_mem
    intro w hw
    obtain ⟨ht,hs,hr⟩ := mainPlan_slot hw
    have hv := congrArg Prod.fst hr
    change w.vid=(queueForestRankResolve (queueInputs pre v pres) 0 w.tau w.slot).1 at hv
    rw [ht] at hv
    have hi := queueRankResolve_selected_iff hs (hh _ (List.mem_of_getElem? hs)) 0 i
    change (w.value.isSome=true ∧ (queueRankResolve pre (mainRequests pre v) 0 w.slot).1=0+i) ↔ _ at hi
    have hp : (w.value.isSome && w.vid==i)=(valueIndex pre (w.request v.shards).key==some i) := by
      apply Bool.eq_iff_iff.mpr
      simpa [hv,queueForestRankResolve,queueInputs] using hi
    rw [hp]
  exact he.trans (mainPlan_useRanks pre v pres i)

theorem queueForestRankResolve_vid (xs : List (PTrie × List ReadRequest)) (base tau slot : Nat) :
    (queueForestRankResolve xs base tau slot).1=(queueForestResolve xs base tau slot).1 := by
  induction xs generalizing base tau with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨pre,rs⟩ := x
    cases tau with
    | zero =>
      simp only [queueForestRankResolve,queueForestResolve,queueRankResolve,queueResolve]
      cases valueIndex pre (rs.getD slot ⟨[],none,.raw⟩).key <;> rfl
    | succ tau => exact ih _ tau

theorem queueForestRankResolve_zero (xs : List (PTrie × List ReadRequest)) (base tau : Nat) :
    (queueForestRankResolve xs base tau 0).2=0 := by
  induction xs generalizing base tau with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨pre,rs⟩ := x
    cases tau with
    | zero =>
      simp only [queueForestRankResolve,queueRankResolve]
      cases valueIndex pre (rs.getD 0 ⟨[],none,.raw⟩).key <;> rfl
    | succ tau => exact ih _ tau

def providerWalkRanks (ws : List Walk) (tau vid : Nat) : List Nat :=
  ws.filterMap (fun w => if w.value.isSome && (w.tau==tau && w.vid==vid) then some w.users else none)

theorem plan_main_counter_class (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (hh : ∀ r ∈ mainRequests pre v, r.Holds pre) (i : Nat) :
    providerWalkRanks (plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)) 0 i =
      List.range' 0 (queueUsers pre (mainRequests pre v) i) := by
  unfold providerWalkRanks plan
  rw [List.filterMap_append]
  have hm : (mainPlan pre v pres.length (queueForestRankResolve (queueInputs pre v pres) 0)).filterMap
      (fun w => if w.value.isSome && (w.tau==0 && w.vid==i) then some w.users else none) =
    (mainPlan pre v pres.length (queueForestRankResolve (queueInputs pre v pres) 0)).filterMap
      (fun w => if w.value.isSome && w.vid==i then some w.users else none) := by
    apply filterMap_congr_mem
    intro w hw
    simp [(mainPlan_slot hw).1]
  rw [hm,mainPlan_counter_class pre v pres hh i]
  simp [implicitPlan,List.filterMap_map,Function.comp_def]

private theorem filterMap_const_count {α β : Type} (xs : List α) (p : α → Bool) (b : β) :
    xs.filterMap (fun x => if p x then some b else none)=List.replicate (xs.countP p) b := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih,List.countP_cons,List.replicate_succ]

theorem implicitPlan_counter_class (pres : List PTrie) (resolve : Resolve) (j vid : Nat)
    {t : PTrie} (ht : pres[j]?=some t) (hv : (missingRequest t).value.isSome=true)
    (hr : resolve (j+1) 0=(vid,0)) :
    providerWalkRanks (implicitPlan pres resolve) (j+1) vid=[0] := by
  unfold providerWalkRanks implicitPlan
  rw [List.filterMap_map]
  have he : pres.zipIdx.filterMap ((fun w : Walk =>
      if w.value.isSome && (w.tau==j+1 && w.vid==vid) then some w.users else none) ∘
      (fun x => (⟨.delayed,x.2+1,0,0,(missingRequest x.1).value,
        (resolve (x.2+1) 0).1,(resolve (x.2+1) 0).2,false,x.2+1==pres.length⟩ : Walk))) =
      pres.zipIdx.filterMap (fun x => if x.2==j then some 0 else none) := by
    apply filterMap_congr_mem
    intro x hx
    obtain ⟨u,k⟩ := x
    by_cases hk : k=j
    · subst k
      have hu := List.mk_mem_zipIdx_iff_getElem?.mp hx
      rw [ht] at hu
      cases hu
      simp [Function.comp_def,hv,hr]
    · simp [Function.comp_def,hk]
  rw [he,filterMap_const_count]
  have hc := List.countP_map (p := fun i => i==j) (f := Prod.snd) (l := pres.zipIdx)
  simp only [Function.comp_def] at hc
  rw [← hc,List.zipIdx_map_snd]
  change List.replicate (List.count j (List.range' 0 pres.length)) 0=[0]
  simp [List.count_range_1',(List.getElem?_eq_some_iff.mp ht).1]

/-- Exact consecutive counter class for every actual provider in the full plan. -/
theorem plan_provider_counter_class {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (hh : ∀ r ∈ mainRequests pre v, r.Holds pre)
    {p : QueueProvider} (hp : p ∈ queueForestProviders 0 0 (queueInputs pre v pres)) :
    providerWalkRanks (plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)) p.tau p.vid =
      List.range' 0 p.users := by
  obtain ⟨j,t,rs,offset,hj,ht,hp',hr⟩ := queueForest_provider_location _ 0 0 p hp
  cases j with
  | zero =>
    simp only [queueInputs,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hj
    obtain ⟨rfl,rfl⟩ := hj
    simp only [queueInputs,queueForestProviders,List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨⟨b,i⟩,hi,rfl⟩ := List.mem_map.mp hp
      simpa only [Nat.zero_add] using plan_main_counter_class pre v pres hh i
    · have hb := queueForestProviders_bounds _ _ _ hp
      simp only [Nat.zero_add,Nat.add_zero] at ht
      omega
  | succ j =>
    simp only [queueInputs,List.getElem?_cons_succ,List.getElem?_map] at hj
    obtain ⟨u,hu,he⟩ := Option.map_eq_some_iff.mp hj
    cases he
    have hus := queueProviders_singleton_users hp'
    obtain ⟨slot,r,hs,hfind,hresolve⟩ := queueProvider_resolver hp'
    have hslot : slot=0 := by
      cases slot with
      | zero => rfl
      | succ n => simp at hs
    subst slot
    simp only [List.getElem?_cons_zero,Option.some.injEq] at hs
    subst r
    have hv : (missingRequest t).value.isSome=true := by
      change t.find keyDelayedIdx=some (some p.bytes) at hfind
      simp [missingRequest,hfind]
    have hresolved : queueForestRankResolve (queueInputs pre v pres) 0 (j+1) 0=(p.vid,0) := by
      apply Prod.ext
      · have he : (queueForestResolve (queueInputs pre v pres) 0 (j+1) 0).1=p.vid :=
          congrArg Prod.fst ((hr 0).trans hresolve)
        exact (queueForestRankResolve_vid _ _ _ _).trans he
      · exact queueForestRankResolve_zero _ _ _
    simp only [Nat.zero_add] at ht
    unfold providerWalkRanks plan
    rw [List.filterMap_append]
    have hmain : (mainPlan pre v pres.length (queueForestRankResolve (queueInputs pre v pres) 0)).filterMap
        (fun w => if w.value.isSome && (w.tau==p.tau && w.vid==p.vid) then some w.users else none)=[] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro w hw
      simp [(mainPlan_slot hw).1,ht]
    rw [hmain,List.nil_append,ht]
    change providerWalkRanks (implicitPlan pres _) (j+1) p.vid = _
    rw [implicitPlan_counter_class pres _ j p.vid hu hv hresolved,hus]
    rfl

end ZkFormal.NearV3.Assembly
