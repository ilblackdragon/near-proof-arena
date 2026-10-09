import ZkFormal.NearV3.Candidates.ExceptLoop
namespace ZkFormal.NearV3.Candidates.ExceptArrayCount

theorem count {α β ε : Type} (xs : List α) (f : α → Array β → Except ε (ForInStep (Array β)))
    (hf : ∀a∈xs,∀b s,f a b=.ok s → ∃b',s=.yield b' ∧ b'.size=b.size+1)
    (b out : Array β) (h : forIn xs b f=.ok out) : out.size=b.size+xs.length := by
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
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
end ZkFormal.NearV3.Candidates.ExceptArrayCount
