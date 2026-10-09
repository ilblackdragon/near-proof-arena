import ZkFormal.NearV3.Candidates.ProcPriorEventUniqueness
namespace ZkFormal.NearV3.Candidates.ProcPriorEventStrictOrder
open NearSpec NearSpec.Bandwidth ProcPriorEvents

theorem write_stamp_injective (ids : List Nat) (rs : List LinkAllowance) (a b : Event)
    (ha:a∈writeEvents ids rs) (hb:b∈writeEvents ids rs) (hs:a.stamp=b.stamp) : a=b := by
  obtain ⟨u,hu,htu,hqa,hla,hia⟩:=write_source ids rs a ha
  obtain ⟨v,hv,htv,hqb,hlb,hib⟩:=write_source ids rs b hb
  have huv:u=v:=by rw [hs,hv] at hu;exact Option.some.inj hu.symm
  subst v
  have hl:a.link=b.link:=Option.some.inj (htu.symm.trans htv)
  cases a;cases b
  simp only at *
  congr <;> grind

theorem key_injective (ids : List Nat) (rs : List LinkAllowance) (a b : Event)
    (ha:a∈events ids rs) (hb:b∈events ids rs) (hl:a.link=b.link) (hs:a.stamp=b.stamp) : a=b := by
  have ha':=(events_perm ids rs).mem_iff.mp ha
  have hb':=(events_perm ids rs).mem_iff.mp hb
  rcases List.mem_append.mp ha' with haw|haq
  · rcases List.mem_append.mp hb' with hbw|hbq
    · exact write_stamp_injective ids rs a b haw hbw hs
    · have hw:=write_before_queries ids rs a haw
      have hq:=(query_source ids rs b hbq).2.1
      omega
  · rcases List.mem_append.mp hb' with hbw|hbq
    · have hw:=write_before_queries ids rs b hbw
      have hq:=(query_source ids rs a haq).2.1
      omega
    · obtain ⟨_,hsa,hqa,hla,hia⟩:=query_source ids rs a haq
      obtain ⟨_,hsb,hqb,hlb,hib⟩:=query_source ids rs b hbq
      rw [hl] at hla hia
      cases a;cases b
      simp only at *
      congr <;> grind

theorem sorted_strict (ids : List Nat) (rs : List LinkAllowance) :
    (events ids rs).Pairwise (fun a b=>a.link<b.link ∨ a.link=b.link ∧ a.stamp<b.stamp) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hs:=List.pairwise_iff_getElem.mp (events_sorted ids rs) i j hi hj hij
  have ha:=List.getElem_mem hi
  have hb:=List.getElem_mem hj
  have hn: (events ids rs)[i]≠(events ids rs)[j]:=by
    intro he
    have hopt:(events ids rs)[i]?=(events ids rs)[j]?:=by
      rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,he]
    have heq:=(ProcPriorEventUniqueness.events_nodup ids rs).getElem?_inj hi |>.mp hopt
    omega
  simp only [precedes,decide_eq_true_eq] at hs
  have hkey:¬((events ids rs)[i].link=(events ids rs)[j].link ∧
      (events ids rs)[i].stamp=(events ids rs)[j].stamp):=
    fun h=>hn (key_injective ids rs _ _ ha hb h.1 h.2)
  omega
end ZkFormal.NearV3.Candidates.ProcPriorEventStrictOrder
