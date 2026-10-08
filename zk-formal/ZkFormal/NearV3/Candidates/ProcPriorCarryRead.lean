import ZkFormal.NearV3.Candidates.ProcPriorCarryValue
namespace ZkFormal.NearV3.Candidates.ProcPriorCarryRead
open NearSpec NearSpec.Bandwidth ProcPriorEvents ProcPriorValues ProcPriorCarry ProcPriorCarryValue

/-- Every actual query receives the value of the linear-time segmented carry.
This establishes the honest memory read equation from native sorted events. -/
theorem query_carry (ids : List Nat) (rs : List LinkAllowance) (pre post : List Event) (e : Event)
    (he:events ids rs=pre++e::post) (hq:e.query=true) : atKey (run pre) e.link=value e := by
  have hem:e∈events ids rs := by rw [he]; simp
  have her:e∈writeEvents ids rs++queryEvents ids rs := (events_perm ids rs).mem_iff.mp hem
  have hqe:e∈queryEvents ids rs := by
    rcases List.mem_append.mp her with hw|hq'
    · obtain ⟨_,_,_,hf,_,_⟩:=write_source ids rs e hw
      rw [hq] at hf
      cases hf
    · exact hq'
  have hstamp:e.stamp=rs.length := (query_source ids rs e hqe).2.1
  have hsorted:=events_sorted ids rs
  rw [he] at hsorted
  obtain ⟨hpre,htail,hcross⟩:=List.pairwise_append.mp hsorted
  have hpk:pre.Pairwise (fun a b=>a.link≤b.link) := hpre.imp (by
    intro a b hab
    simp only [precedes,decide_eq_true_eq] at hab
    omega)
  have hbound:∀ a∈pre,a.link≤e.link := by
    intro a ha
    have hh:=hcross a ha e (by simp)
    simp only [precedes,decide_eq_true_eq] at hh
    omega
  have hpost:∀ x∈post,x.link=e.link→x.query=true := by
    intro x hx hk
    have hxm:x∈events ids rs := by rw [he]; simp [hx]
    have hxr:x∈writeEvents ids rs++queryEvents ids rs := (events_perm ids rs).mem_iff.mp hxm
    rcases List.mem_append.mp hxr with hw|hquery
    · have hlt:=write_before_queries ids rs x hw
      have hs:precedes e x=true := (List.pairwise_cons.mp htail).1 x hx
      simp only [precedes,decide_eq_true_eq] at hs
      omega
    · exact (query_source ids rs x hquery).2.2.1
  have hignore:foldKey (pre++e::post) e.link=foldKey pre e.link := ignored_tail pre (e::post) e.link (by
    intro x hx hk
    rcases List.mem_cons.mp hx with rfl|hx
    · exact hq
    · exact hpost x hx hk)
  have hfull:=full_query ids rs e hqe
  rw [he,hignore] at hfull
  rw [run_extreme pre hpk e.link hbound,hfull]

end ZkFormal.NearV3.Candidates.ProcPriorCarryRead
