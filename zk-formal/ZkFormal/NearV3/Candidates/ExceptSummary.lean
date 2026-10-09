import ZkFormal.NearV3.Candidates.ExceptLoop
namespace ZkFormal.NearV3.Candidates.ExceptSummary

theorem summary {α β γ ε : Type} (xs : List α) (f : α → β → Except ε (ForInStep β))
    (view : β → List γ) (item : α → γ)
    (hf : ∀a∈xs,∀b s,f a b=.ok s → ∃b',s=.yield b' ∧ view b'=view b++[item a])
    (b out : β) (h : forIn xs b f=.ok out) : view out=view b++xs.map item := by
  induction xs generalizing b with
  | nil =>
    simp only [List.forIn_nil] at h
    cases h
    simp
  | cons a xs ih =>
    rw [List.forIn_cons] at h
    cases he : f a b with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok s =>
      rcases hf a (by simp) b s he with ⟨next,rfl,hn⟩
      simp only [he,bind,Except.bind] at h
      rw [ih (fun a ha=>hf a (by simp [ha])) next h,hn]
      simp [List.append_assoc]

theorem from_empty {α β γ ε : Type} (xs : List α) (f : α → β → Except ε (ForInStep β))
    (view : β → List γ) (item : α → γ)
    (hf : ∀a∈xs,∀b s,f a b=.ok s → ∃b',s=.yield b' ∧ view b'=view b++[item a])
    (b out : β) (hb : view b=[]) (h : forIn xs b f=.ok out) : view out=xs.map item := by
  simpa [hb] using summary xs f view item hf b out h
end ZkFormal.NearV3.Candidates.ExceptSummary
