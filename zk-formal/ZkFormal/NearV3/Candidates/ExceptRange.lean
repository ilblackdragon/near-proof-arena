import ZkFormal.NearV3.Candidates.ExceptLoop
namespace ZkFormal.NearV3.Candidates.ExceptRange

/-- Index-sensitive invariant for a successful native range loop whose body
always continues. The final index is the actual number of executed iterations. -/
theorem invariant {β ε : Type} (f : Nat → β → Except ε (ForInStep β))
    (P : Nat → β → Prop) (start count : Nat)
    (hf : ∀i,start≤i → i<start+count → ∀b,P i b → ∀s,f i b=.ok s →
      ∃b',s=.yield b' ∧ P (i+1) b')
    (b out : β) (hb : P start b)
    (h : forIn (List.range' start count) b f=.ok out) : P (start+count) out := by
  induction count generalizing start b with
  | zero =>
    simp only [List.range'_zero,List.forIn_nil] at h
    cases h
    simpa using hb
  | succ count ih =>
    rw [List.range'_succ,List.forIn_cons] at h
    cases he : f start b with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok s =>
      rcases hf start (by omega) (by omega) b hb s he with ⟨next,rfl,hn⟩
      simp only [he,bind,Except.bind] at h
      have ht := ih (start+1) (fun i h0 h1=>hf i (by omega) (by omega)) next hn h
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem range_invariant {β ε : Type} (f : Nat → β → Except ε (ForInStep β))
    (P : Nat → β → Prop) (count : Nat)
    (hf : ∀i,i<count → ∀b,P i b → ∀s,f i b=.ok s → ∃b',s=.yield b' ∧ P (i+1) b')
    (b out : β) (hb : P 0 b) (h : forIn (List.range count) b f=.ok out) : P count out := by
  rw [List.range_eq_range'] at h
  simpa using invariant f P 0 count (fun i _ hi=>hf i (by simpa using hi)) b out hb h
end ZkFormal.NearV3.Candidates.ExceptRange
