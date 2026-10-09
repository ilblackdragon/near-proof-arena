import ZkFormal.NearV3.Candidates.ProcCodecExecutionIndex
namespace ZkFormal.NearV3.Candidates.ProcCodecExecutionAdjacentIndex
open ProcCodecExecutionTrace ProcCodecExecutionIndex

theorem at_pair {α σ ε : Type} {step : α→σ→Except ε (ForInStep σ)}
    (xs : List α) (s out : σ) (h : Steps step xs s out) (i : Nat) (hi : i+1<xs.length) :
    ∃before mid after,Steps step (xs.take i) s before ∧
      step xs[i] before=.ok (.yield mid) ∧ step xs[i+1] mid=.ok (.yield after) ∧
      Steps step (xs.drop (i+2)) after out := by
  induction xs generalizing s i with
  | nil => simp at hi
  | cons a xs ih =>
    cases h with
    | cons hh ht =>
      cases i with
      | zero =>
        cases xs with
        | nil => simp at hi
        | cons b bs =>
          cases ht with
          | cons hb tail => exact ⟨_,_,_,.nil _,hh,hb,tail⟩
      | succ i =>
        obtain ⟨before,mid,after,hpre,ha,hb,hpost⟩ := ih _ ht i (by simp at hi; omega)
        exact ⟨before,mid,after,.cons hh hpre,ha,hb,hpost⟩

theorem pair_span {α β σ ε : Type} {step : α→σ→Except ε (ForInStep σ)}
    (rows : σ→List β) (count : Nat) (xs : List α) (s out : σ)
    (h : Steps step xs s out)
    (hw : ∀a∈xs,∀before after,step a before=.ok (.yield after)→
      ∃added,rows after=rows before++added ∧ added.length=count)
    (i : Nat) (hi : i+1<xs.length) :
    ∃before mid after suffix,
      step xs[i] before=.ok (.yield mid) ∧ step xs[i+1] mid=.ok (.yield after) ∧
      (rows before).length=(rows s).length+count*i ∧ rows out=rows after++suffix := by
  obtain ⟨before,mid,after,hpre,ha,hb,hpost⟩ := at_pair xs s out h i hi
  obtain ⟨pre,hpr,hpl⟩ := span rows count _ s before hpre
    (fun a ha=>hw a (List.mem_of_mem_take ha))
  obtain ⟨post,hpo,_⟩ := span rows count _ after out hpost
    (fun a ha=>hw a (List.mem_of_mem_drop ha))
  refine ⟨before,mid,after,post,ha,hb,?_,hpo⟩
  rw [hpr,List.length_append,hpl,List.length_take,Nat.min_eq_left (by omega)]
end ZkFormal.NearV3.Candidates.ProcCodecExecutionAdjacentIndex
