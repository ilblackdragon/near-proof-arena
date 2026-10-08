import ZkFormal.NearV3.Candidates.ProcPriorBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorWinner
open NearSpec NearSpec.Bandwidth ProcPriorLookup

def winner (ids : List Nat) (rs : List LinkAllowance) (l : Nat) : Option LinkAllowance :=
  (rs.filter fun r=>target ids r==some l).getLast?

theorem matching_writes (ids : List Nat) (rs : List LinkAllowance) (l : Nat) :
    (writes ids rs).filter (fun p=>p.1==l)=
      (rs.filter fun r=>target ids r==some l).map (fun r=>(l,r.allowance)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [writes] at ih
    simp only [writes,List.filterMap_cons,List.filter_cons]
    cases ht:target ids r with
    | none => simpa [ht,writes] using ih
    | some k =>
      by_cases hk:k=l
      · subst k
        simpa only [Option.map_some,List.filter_cons,beq_self_eq_true,ite_true,List.map_cons,List.cons.injEq,true_and] using ih
      · simpa [hk] using ih

theorem allowance_winner (ids : List Nat) (st : State) (l : Nat)
    (hl:l<ids.length*ids.length) :
    (ProcActualInput.allowances ids st)[l]? = some ((winner ids st.links l).map (·.allowance) |>.getD 0) := by
  rw [allowance_last ids st l hl,matching_writes,List.getLast?_map]
  simp [winner,Option.map_map,Function.comp_def]

theorem winner_member (ids : List Nat) (rs : List LinkAllowance) (l : Nat) (r : LinkAllowance)
    (h : winner ids rs l=some r) : r∈rs ∧ target ids r=some l := by
  have hm:=List.mem_of_getLast? h
  simpa only [List.mem_filter,beq_iff_eq] using hm

theorem winner_none (ids : List Nat) (rs : List LinkAllowance) (l : Nat)
    (h : winner ids rs l=none) : ∀ r∈rs,target ids r≠some l := by
  have hn:=List.getLast?_eq_none_iff.mp h
  simpa only [List.filter_eq_nil_iff,Bool.eq_false_iff,beq_iff_eq] using hn

/-- The chosen source is followed only by records targeting other links. -/
theorem winner_last (ids : List Nat) (rs : List LinkAllowance) (l : Nat) (r : LinkAllowance)
    (h : winner ids rs l=some r) :
    ∃ before after, rs=before++r::after ∧ target ids r=some l ∧
      ∀ a∈after,target ids a≠some l := by
  simp only [winner,List.getLast?_filter] at h
  obtain ⟨hm,before,after,he,hn⟩:=List.find?_eq_some_iff_append.mp h
  refine ⟨after.reverse,before.reverse,?_,by simpa using hm,?_⟩
  · have hr:=congrArg List.reverse he
    simpa only [List.reverse_reverse,List.reverse_append,List.reverse_cons,List.append_assoc,List.singleton_append] using hr
  · intro a ha
    have hh:=hn a (List.mem_reverse.mp ha)
    simpa using hh

end ZkFormal.NearV3.Candidates.ProcPriorWinner
