import ZkFormal.NearV3.Sched.Gen.Run
namespace ZkFormal.NearV3.Candidates.ExceptLoop

def StepInv {β : Type} (P : β → Prop) (s : ForInStep β) : Prop :=
  match s with | .done b => P b | .yield b => P b

/-- A successful native for-in loop preserves an ordinary state invariant,
including its early-break case. Errors do not manufacture an output witness. -/
theorem invariant {α β ε : Type} (xs : List α) (f : α → β → Except ε (ForInStep β))
    (P : β → Prop) (hf : ∀a∈xs,∀b,P b → ∀s,f a b=.ok s → StepInv P s)
    (b out : β) (hb : P b) (h : forIn xs b f=.ok out) : P out := by
  induction xs generalizing b with
  | nil =>
    simp only [List.forIn_nil] at h
    cases h
    exact hb
  | cons a xs ih =>
    rw [List.forIn_cons] at h
    cases he : f a b with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok s =>
      have hs := hf a (by simp) b hb s he
      cases s with
      | done next =>
        simp only [he,bind,Except.bind] at h
        cases h
        exact hs
      | yield next =>
        simp only [he,bind,Except.bind] at h
        exact ih (fun a ha=>hf a (by simp [ha])) next hs h
end ZkFormal.NearV3.Candidates.ExceptLoop
