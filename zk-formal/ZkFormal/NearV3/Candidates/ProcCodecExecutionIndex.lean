import ZkFormal.NearV3.Candidates.ProcCodecExecutionTrace
namespace ZkFormal.NearV3.Candidates.ProcCodecExecutionIndex
open ProcCodecExecutionTrace

theorem at_index {α σ ε : Type} {step : α→σ→Except ε (ForInStep σ)}
    (xs : List α) (s out : σ) (h : Steps step xs s out) (i : Nat) (hi : i<xs.length) :
    ∃before after,Steps step (xs.take i) s before ∧
      step xs[i] before=.ok (.yield after) ∧ Steps step (xs.drop (i+1)) after out := by
  induction xs generalizing s i with
  | nil => simp at hi
  | cons a xs ih =>
    cases h with
    | cons hh ht =>
      cases i with
      | zero => exact ⟨_,_,.nil _,hh,ht⟩
      | succ i =>
        obtain ⟨before,after,hpre,he,hpost⟩ := ih _ ht i (by simp at hi; omega)
        exact ⟨before,after,.cons hh hpre,he,hpost⟩

theorem span {α β σ ε : Type} {step : α→σ→Except ε (ForInStep σ)}
    (rows : σ→List β) (count : Nat) (xs : List α) (s out : σ)
    (h : Steps step xs s out)
    (hw : ∀a∈xs,∀before after,step a before=.ok (.yield after)→
      ∃added,rows after=rows before++added ∧ added.length=count) :
    ∃added,rows out=rows s++added ∧ added.length=count*xs.length := by
  induction xs generalizing s with
  | nil => cases h; exact ⟨[],by simp,by simp⟩
  | cons a xs ih =>
    cases h with
    | cons hh ht =>
      obtain ⟨head,he,hl⟩ := hw a (by simp) _ _ hh
      obtain ⟨tail,te,tl⟩ := ih _ ht (fun x hx=>hw x (by simp [hx]))
      refine ⟨head++tail,?_,?_⟩
      · rw [te,he,List.append_assoc]
      · rw [List.length_append,hl,tl,List.length_cons,Nat.mul_add]
        omega

/-- Exact step provenance together with its output offset and preserved suffix. -/
theorem indexed_span {α β σ ε : Type} {step : α→σ→Except ε (ForInStep σ)}
    (rows : σ→List β) (count : Nat) (xs : List α) (s out : σ)
    (h : Steps step xs s out)
    (hw : ∀a∈xs,∀before after,step a before=.ok (.yield after)→
      ∃added,rows after=rows before++added ∧ added.length=count)
    (i : Nat) (hi : i<xs.length) :
    ∃before after added suffix,
      step xs[i] before=.ok (.yield after) ∧
      (rows before).length=(rows s).length+count*i ∧
      rows after=rows before++added ∧ added.length=count ∧
      rows out=rows after++suffix := by
  obtain ⟨before,after,hpre,he,hpost⟩ := at_index xs s out h i hi
  obtain ⟨pre,hpr,hpl⟩ := span rows count _ s before hpre
    (fun a ha=>hw a (List.mem_of_mem_take ha))
  obtain ⟨post,hpo,_⟩ := span rows count _ after out hpost
    (fun a ha=>hw a (List.mem_of_mem_drop ha))
  obtain ⟨added,har,hal⟩ := hw xs[i] (List.getElem_mem hi) before after he
  refine ⟨before,after,added,post,he,?_,har,hal,hpo⟩
  rw [hpr,List.length_append,hpl,List.length_take,Nat.min_eq_left (by omega)]
end ZkFormal.NearV3.Candidates.ProcCodecExecutionIndex
