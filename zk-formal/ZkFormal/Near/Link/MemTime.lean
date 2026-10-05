import ZkFormal.Near.Link.MemBus

/-!
# ZkFormal.Near.Link.MemTime — the last write time of a slot

`lastW s k r` is the time of the last write to slot `k` before receipt `r`
(receipt `r'` writes at time `r' + 1` to slot `s r'`; the initial write is at `0`).
-/

namespace ZkFormal.Near

namespace Link

def lastW (s : Nat → Nat) (k : Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => if s r = k then r + 1 else lastW s k r

variable (s : Nat → Nat) (k : Nat)

theorem lastW_le : ∀ r, lastW s k r ≤ r
  | 0 => Nat.le_refl _
  | r + 1 => by
    unfold lastW; split
    · exact Nat.le_refl _
    · have := lastW_le r; omega

theorem lastW_cases : ∀ r, lastW s k r = 0 ∨ ∃ r0, r0 < r ∧ s r0 = k ∧ lastW s k r = r0 + 1
  | 0 => .inl rfl
  | r + 1 => by
    unfold lastW; split
    · next h => exact .inr ⟨r, by omega, h, rfl⟩
    · rcases lastW_cases r with h | ⟨r0, h1, h2, h3⟩
      · exact .inl h
      · exact .inr ⟨r0, by omega, h2, h3⟩

theorem le_lastW : ∀ r r', r' < r → s r' = k → r' + 1 ≤ lastW s k r
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | r + 1, r', h, hs => by
    unfold lastW; split
    · omega
    · next hne =>
      have : r' ≠ r := fun e => hne (e ▸ hs)
      exact le_lastW r r' (by omega) hs

theorem lastW_eq_of {t : Nat} (ht : t = 0 ∨ (0 < t ∧ s (t - 1) = k)) :
    ∀ r1, t ≤ r1 → (∀ r'', t ≤ r'' → r'' < r1 → s r'' ≠ k) → lastW s k r1 = t
  | 0, h, _ => by unfold lastW; omega
  | r1 + 1, h, hn => by
    unfold lastW
    split
    · next hs =>
      rcases Nat.eq_or_lt_of_le h with e | e
      · exact e.symm
      · exact absurd hs (hn r1 (by omega) (by omega))
    · next hs =>
      rcases Nat.eq_or_lt_of_le h with e | e
      · subst e
        rcases ht with ht | ⟨-, ht⟩
        · omega
        · simp at ht; exact absurd ht hs
      · exact lastW_eq_of ht r1 (by omega) (fun r'' h1 h2 => hn r'' h1 (by omega))

theorem exists_first (t : Nat) : ∀ r0, t ≤ r0 → s r0 = k →
    ∃ r1, t ≤ r1 ∧ r1 ≤ r0 ∧ s r1 = k ∧ ∀ r'', t ≤ r'' → r'' < r1 → s r'' ≠ k := by
  intro r0
  induction r0 using Nat.strongRecOn with
  | _ r0 ih =>
    intro h1 h2
    by_cases hex : ∃ r'', t ≤ r'' ∧ r'' < r0 ∧ s r'' = k
    · obtain ⟨r'', a, b, c⟩ := hex
      obtain ⟨r1, e1, e2, e3, e4⟩ := ih r'' b a c
      exact ⟨r1, e1, by omega, e3, e4⟩
    · exact ⟨r0, h1, Nat.le_refl _, h2, fun r'' a b c => hex ⟨r'', a, b, c⟩⟩

end Link

end ZkFormal.Near
