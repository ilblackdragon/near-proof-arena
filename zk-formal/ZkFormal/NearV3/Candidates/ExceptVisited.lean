import ZkFormal.NearV3.Candidates.ExceptLoop
namespace ZkFormal.NearV3.Candidates.ExceptVisited

/-- Successful loops without early exits certify every input, not merely the
returned accumulator. This extracts guards from validation-only loops. -/
theorem visited {α β ε : Type} (xs : List α) (f : α → β → Except ε (ForInStep β))
    (P : α → Prop)
    (hf : ∀a∈xs,∀b s,f a b=.ok s → P a ∧ ∃b',s=.yield b')
    (b out : β) (h : forIn xs b f=.ok out) : ∀a∈xs,P a := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih =>
    rw [List.forIn_cons] at h
    cases he : f a b with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok s =>
      rcases hf a (by simp) b s he with ⟨ha,next,rfl⟩
      simp only [he,bind,Except.bind] at h
      have hs := ih (fun x hx=>hf x (by simp [hx])) next h
      simpa only [List.forall_mem_cons] using And.intro ha hs

theorem array_visited {α β ε : Type} (xs : Array α) (f : α → β → Except ε (ForInStep β))
    (P : α → Prop)
    (hf : ∀a∈xs.toList,∀b s,f a b=.ok s → P a ∧ ∃b',s=.yield b')
    (b out : β) (h : forIn xs b f=.ok out) : ∀a∈xs.toList,P a :=
  visited xs.toList f P hf b out (by simpa using h)
end ZkFormal.NearV3.Candidates.ExceptVisited
