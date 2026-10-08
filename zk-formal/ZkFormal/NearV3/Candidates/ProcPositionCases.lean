import ZkFormal.NearV3.Candidates.ProcEntryPosition
namespace ZkFormal.NearV3.Candidates.ProcPositionCases
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcEntryPosition

theorem flat_position {α β : Type} (f : α→List β) (xs : List α) (r : Nat)
    (hr : r<(xs.flatMap f).length) :
    ∃ pre a post j,xs=pre++a::post ∧ j<(f a).length ∧ r=(pre.flatMap f).length+j := by
  induction xs generalizing r with
  | nil => simp at hr
  | cons a xs ih =>
    by_cases h : r<(f a).length
    · exact ⟨[],a,xs,r,rfl,h,by simp⟩
    · have ht : r-(f a).length<(xs.flatMap f).length := by
        simp only [List.flatMap_cons,List.length_append] at hr
        omega
      obtain ⟨pre,b,post,j,he,hj,hpos⟩ := ih _ ht
      refine ⟨a::pre,b,post,j,?_,hj,?_⟩
      · simp [he]
      · simp only [List.flatMap_cons,List.length_append]
        omega

theorem active_cases (R : Run) (r : Nat) (hr : r<(procVs R).length) :
    r<16 ∨ ∃ pre rd post,R.rounds=pre++rd::post ∧
      (r=roundStart R pre ∨ ∃ i,i<rd.entries.toArray.size ∧ r=roundStart R pre+1+i) := by
  by_cases hk : r<16
  · exact Or.inl hk
  · right
    have hf : r-16<(R.rounds.flatMap (roundVs R)).length := by
      simp only [procVs,List.length_append,keyVs,List.length_map,List.length_range] at hr
      omega
    obtain ⟨pre,rd,post,j,he,hj,hpos⟩ := flat_position (roundVs R) R.rounds (r-16) hf
    refine ⟨pre,rd,post,he,?_⟩
    have hp : r=roundStart R pre+j := by
      simp only [roundStart,List.length_append,keyVs,List.length_map,List.length_range]
      omega
    cases j with
    | zero => left; simpa using hp
    | succ i =>
      right
      refine ⟨i,?_,?_⟩
      · simpa [roundVs] using hj
      · omega
end ZkFormal.NearV3.Candidates.ProcPositionCases
