import ZkFormal.NearV3.Candidates.ProcPriorIds
namespace ZkFormal.NearV3.Candidates.ProcPriorIdOrder
open NearSpec NearSpec.Bandwidth ProcPriorIds

def within (a b : Event) : Prop := rank a<rank b ∨ rank a=rank b ∧ a.ordinal≤b.ordinal

theorem request_order (ids : List Nat) (rs : List LinkAllowance) :
    (requestEvents ids rs).Pairwise (fun a b=>a.ordinal<b.ordinal) := by
  have hz:rs.zipIdx.Pairwise (fun a b=>a.2<b.2) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [List.getElem_zipIdx,Nat.zero_add] using hij
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    simp
  · apply hz.imp
    intro a b hab x hx y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> dsimp at * <;> omega

theorem public_order (ids : List Nat) : (publicEvents ids).Pairwise (fun a b=>a.ordinal≤b.ordinal) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [publicEvents,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
  omega

theorem raw_order (ids : List Nat) (rs : List LinkAllowance) :
    (publicEvents ids++requestEvents ids rs).Pairwise within := by
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · apply (public_order ids).imp_of_mem
    intro a b ha hb hab
    have h1: a.isPublic=true := (public_source ids a ha).2.1
    have h2: b.isPublic=true := (public_source ids b hb).2.1
    simp [within,rank,h1,h2,hab]
  · apply (request_order ids rs).imp_of_mem
    intro a b ha hb hab
    obtain ⟨_,_,_,h1,_,_⟩:=request_source ids rs a ha
    obtain ⟨_,_,_,h2,_,_⟩:=request_source ids rs b hb
    simp [within,rank,h1,h2,Nat.le_of_lt hab]
  · intro a ha b hb
    have h1: a.isPublic=true := (public_source ids a ha).2.1
    obtain ⟨_,_,_,h2,_,_⟩:=request_source ids rs b hb
    simp [within,rank,h1,h2]

theorem event_unique (ids : List Nat) (rs : List LinkAllowance) (a b : Event)
    (ha:a∈publicEvents ids++requestEvents ids rs) (hb:b∈publicEvents ids++requestEvents ids rs)
    (hk:a.key=b.key) (hr:rank a=rank b) (ho:a.ordinal=b.ordinal) : a=b := by
  rcases List.mem_append.mp ha with ha|ha <;> rcases List.mem_append.mp hb with hb|hb
  · obtain ⟨_,hpa,hra⟩:=public_source ids a ha
    obtain ⟨_,hpb,hrb⟩:=public_source ids b hb
    cases a; cases b; simp_all
  · have hpa:= (public_source ids a ha).2.1
    obtain ⟨_,_,_,hpb,_,_⟩:=request_source ids rs b hb
    simp [rank,hpa,hpb] at hr
  · have hpb:= (public_source ids b hb).2.1
    obtain ⟨_,_,_,hpa,_,_⟩:=request_source ids rs a ha
    simp [rank,hpa,hpb] at hr
  · obtain ⟨_,_,_,hpa,hra,_⟩:=request_source ids rs a ha
    obtain ⟨_,_,_,hpb,hrb,_⟩:=request_source ids rs b hb
    cases a; cases b; simp_all

/-- Within every ID group, original public indices precede all requests;
therefore duplicate layout IDs select the first original index. -/
theorem per_id_order (ids : List Nat) (rs : List LinkAllowance) (key : Nat) :
    (events ids rs).filter (fun e=>e.key==key)=
    (publicEvents ids++requestEvents ids rs).filter (fun e=>e.key==key) := by
  apply List.Perm.eq_of_pairwise (le:=within)
  · intro a b ha hb hab hba
    obtain ⟨ham,hak⟩:=List.mem_filter.mp ha
    obtain ⟨hbm,hbk⟩:=List.mem_filter.mp hb
    have ham':a∈publicEvents ids++requestEvents ids rs := (events_perm ids rs).mem_iff.mp ham
    have hak':a.key=key := of_decide_eq_true hak
    have hbk':b.key=key := of_decide_eq_true hbk
    unfold within at hab hba
    exact event_unique ids rs a b ham' hbm (by omega) (by omega) (by omega)
  · apply ((events_sorted ids rs).filter (fun e=>e.key==key)).imp_of_mem
    intro a b ha hb hab
    have hak:a.key=key := of_decide_eq_true (List.mem_filter.mp ha).2
    have hbk:b.key=key := of_decide_eq_true (List.mem_filter.mp hb).2
    simp only [precedes,decide_eq_true_eq] at hab
    unfold within
    omega
  · exact (raw_order ids rs).filter _
  · exact (events_perm ids rs).filter _

end ZkFormal.NearV3.Candidates.ProcPriorIdOrder
