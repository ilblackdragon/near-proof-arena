import ZkFormal.NearV3.Candidates.ProcPriorEvents
namespace ZkFormal.NearV3.Candidates.ProcPriorEventOrder
open NearSpec NearSpec.Bandwidth ProcPriorLookup ProcPriorSummary ProcPriorEvents

theorem write_order (ids : List Nat) (rs : List LinkAllowance) :
    (writeEvents ids rs).Pairwise (fun a b=>a.stamp<b.stamp) := by
  have hz:rs.zipIdx.Pairwise (fun a b=>a.2<b.2) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [List.getElem_zipIdx,Nat.zero_add] using hij
  apply hz.filterMap (fun (r,j)=>(target ids r).map fun l=>Event.mk l j false (low r.allowance) (big r.allowance))
  intro a b hab ea hea eb heb
  cases ha:target ids a.1 <;> cases hb:target ids b.1 <;> simp [ha,hb] at hea heb
  next la lb => subst ea; subst eb; exact hab

theorem raw_order (ids : List Nat) (rs : List LinkAllowance) :
    (writeEvents ids rs++queryEvents ids rs).Pairwise (fun a b=>a.stamp≤b.stamp) := by
  apply List.pairwise_append.mpr
  refine ⟨(write_order ids rs).imp (fun h=>Nat.le_of_lt h),?_,?_⟩
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj _
    have h1:= (query_source ids rs _ (List.getElem_mem hi)).2.1
    have h2:= (query_source ids rs _ (List.getElem_mem hj)).2.1
    omega
  · intro a ha b hb
    have h1:=write_before_queries ids rs a ha
    have h2: b.stamp=rs.length := (query_source ids rs b hb).2.1
    omega

theorem event_unique (ids : List Nat) (rs : List LinkAllowance) (a b : Event)
    (ha:a∈writeEvents ids rs++queryEvents ids rs) (hb:b∈writeEvents ids rs++queryEvents ids rs)
    (hk:a.link=b.link) (ht:a.stamp=b.stamp) : a=b := by
  rcases List.mem_append.mp ha with ha|ha <;> rcases List.mem_append.mp hb with hb|hb
  · obtain ⟨ra,hra,hka,hqa,hla,hba⟩:=write_source ids rs a ha
    obtain ⟨rb,hrb,hkb,hqb,hlb,hbb⟩:=write_source ids rs b hb
    rw [ht,hrb] at hra
    cases Option.some.inj hra
    cases a; cases b; simp_all
  · have h1:=write_before_queries ids rs a ha
    have h2: b.stamp=rs.length := (query_source ids rs b hb).2.1
    omega
  · have h1:=write_before_queries ids rs b hb
    have h2: a.stamp=rs.length := (query_source ids rs a ha).2.1
    omega
  · obtain ⟨_,_,hqa,hla,hba⟩:=query_source ids rs a ha
    obtain ⟨_,_,hqb,hlb,hbb⟩:=query_source ids rs b hb
    cases a; cases b; simp_all

/-- Sorting groups links while preserving every original write in native order. -/
theorem per_link_order (ids : List Nat) (rs : List LinkAllowance) (l : Nat) :
    (events ids rs).filter (fun e=>e.link==l)=
    (writeEvents ids rs++queryEvents ids rs).filter (fun e=>e.link==l) := by
  apply List.Perm.eq_of_pairwise (le:=fun a b=>a.stamp≤b.stamp)
  · intro a b ha hb hab hba
    obtain ⟨ham,hak⟩:=List.mem_filter.mp ha
    obtain ⟨hbm,hbk⟩:=List.mem_filter.mp hb
    have ham':a∈writeEvents ids rs++queryEvents ids rs := (events_perm ids rs).mem_iff.mp ham
    have hak':a.link=l := of_decide_eq_true hak
    have hbk':b.link=l := of_decide_eq_true hbk
    exact event_unique ids rs a b ham' hbm (by omega) (by omega)
  · apply ((events_sorted ids rs).filter (fun e=>e.link==l)).imp_of_mem
    intro a b ha hb hab
    have hak:a.link=l := of_decide_eq_true (List.mem_filter.mp ha).2
    have hbk:b.link=l := of_decide_eq_true (List.mem_filter.mp hb).2
    simp only [precedes,decide_eq_true_eq] at hab
    omega
  · exact (raw_order ids rs).filter _
  · exact (events_perm ids rs).filter _

end ZkFormal.NearV3.Candidates.ProcPriorEventOrder
