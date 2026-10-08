import ZkFormal.NearV3.Candidates.ProcPriorIdCarryValue
namespace ZkFormal.NearV3.Candidates.ProcPriorIdCarryRead
open NearSpec NearSpec.Bandwidth ProcPriorIds ProcPriorIdValue ProcPriorIdCarry ProcPriorIdCarryValue

/-- Every actual query receives the value of the linear-time segmented carry.
This establishes the honest memory read equation from native sorted events. -/
theorem query_carry (ids : List Nat) (rs : List LinkAllowance) (pre post : List Event) (e : Event)
    (he:events ids rs=pre++e::post) (hq:e.isPublic=false) : atKey (run pre) e.key=e.result := by
  have hem:e∈events ids rs := by rw [he]; simp
  have her:e∈publicEvents ids++requestEvents ids rs := (events_perm ids rs).mem_iff.mp hem
  have hqe:e∈requestEvents ids rs := by
    rcases List.mem_append.mp her with hw|hq'
    · have hf:=(public_source ids e hw).2.1
      rw [hq] at hf
      cases hf
    · exact hq'
  have hsorted:=events_sorted ids rs
  rw [he] at hsorted
  obtain ⟨hpre,htail,hcross⟩:=List.pairwise_append.mp hsorted
  have hpk:pre.Pairwise (fun a b=>a.key≤b.key) := hpre.imp (by
    intro a b hab
    simp only [precedes,decide_eq_true_eq] at hab
    omega)
  have hbound:∀ a∈pre,a.key≤e.key := by
    intro a ha
    have hh:=hcross a ha e (by simp)
    simp only [precedes,decide_eq_true_eq] at hh
    omega
  have hpost:∀ x∈post,x.key=e.key→x.isPublic=false := by
    intro x hx hk
    have hs:precedes e x=true := (List.pairwise_cons.mp htail).1 x hx
    cases hp:x.isPublic with
    | false => rfl
    | true =>
      simp [precedes,rank,hq,hp,hk] at hs
  have hignore:foldKey (pre++e::post) e.key=foldKey pre e.key := ignored_tail pre (e::post) e.key (by
    intro x hx hk
    rcases List.mem_cons.mp hx with rfl|hx
    · exact hq
    · exact hpost x hx hk)
  have hfull:=full_query ids rs e hqe
  rw [he,hignore] at hfull
  rw [run_extreme pre hpk e.key hbound,hfull]

end ZkFormal.NearV3.Candidates.ProcPriorIdCarryRead
