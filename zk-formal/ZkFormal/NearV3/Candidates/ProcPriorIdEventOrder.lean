import ZkFormal.NearV3.Candidates.ProcPriorEventUniqueness
import ZkFormal.NearV3.Candidates.ProcPriorIds
namespace ZkFormal.NearV3.Candidates.ProcPriorIdEventOrder
open NearSpec NearSpec.Bandwidth ProcPriorIds

theorem public_order (ids : List Nat) :
    (publicEvents ids).Pairwise (fun a b=>a.ordinal<b.ordinal) := by
  exact List.Pairwise.map _ (fun a b h=>h) (ProcPriorEventUniqueness.zip_order ids)

theorem request_order (ids : List Nat) (rs : List LinkAllowance) :
    (requestEvents ids rs).Pairwise (fun a b=>a.ordinal<b.ordinal) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a ha
    simp
  · apply (ProcPriorEventUniqueness.zip_order rs).imp
    intro a b hab x hx y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp only <;> omega

theorem nodup (ids : List Nat) (rs : List LinkAllowance) : (events ids rs).Nodup := by
  apply (events_perm ids rs).nodup_iff.mpr
  apply List.nodup_append.mpr
  refine ⟨(public_order ids).imp (fun h he=>by cases he;omega),
    (request_order ids rs).imp (fun h he=>by cases he;omega),?_⟩
  intro a ha b hb he
  obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ha
  obtain ⟨y,hy,hb⟩:=List.mem_flatMap.mp hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl <;> have hh:=congrArg Event.isPublic he <;> cases hh

theorem public_key (ids : List Nat) (rs : List LinkAllowance) (a : Event)
    (ha:a∈events ids rs) (hp:a.isPublic=true) : a.result=some a.ordinal := by
  have hm:=(events_perm ids rs).mem_iff.mp ha
  rcases List.mem_append.mp hm with hpub|hreq
  · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hpub
    rfl
  · obtain ⟨y,hy,hm⟩:=List.mem_flatMap.mp hreq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl <;> cases hp

theorem public_strict (ids : List Nat) (rs : List LinkAllowance)
    (i j : Nat) (hi:i<(events ids rs).length) (hj:j<(events ids rs).length) (hij:i<j)
    (hk:(events ids rs)[i].key=(events ids rs)[j].key)
    (ha:(events ids rs)[i].isPublic=true) (hb:(events ids rs)[j].isPublic=true) :
    (events ids rs)[i].ordinal<(events ids rs)[j].ordinal := by
  have hs:=List.pairwise_iff_getElem.mp (events_sorted ids rs) i j hi hj hij
  simp only [precedes,decide_eq_true_eq,rank,ha,hb,ite_true,hk] at hs
  have hra:=public_key ids rs _ (List.getElem_mem hi) ha
  have hrb:=public_key ids rs _ (List.getElem_mem hj) hb
  have hn:(events ids rs)[i]≠(events ids rs)[j]:=by
    intro he
    have hopt:(events ids rs)[i]?=(events ids rs)[j]?:=by
      rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,he]
    have heq:=(nodup ids rs).getElem?_inj hi |>.mp hopt
    omega
  have ho:(events ids rs)[i].ordinal≠(events ids rs)[j].ordinal:=by
    intro he
    apply hn
    cases hia:(events ids rs)[i] with
    | mk ak ap ao ar=>
      cases hja:(events ids rs)[j] with
      | mk bk bp bo br=>
        simp only [hia,hja] at hk ha hb hra hrb he
        congr <;> grind
  omega
end ZkFormal.NearV3.Candidates.ProcPriorIdEventOrder
