import ZkFormal.Near.Render.Proof.BusCommon
/- Generic timestamp conservation adapted from Near/Render/Proof/MemChain.lean.
The recurrence and permutation proof are unchanged; Ext and its receipt
length are replaced by an arbitrary slot function and an explicit length. -/
namespace ZkFormal.NearV3.Rcpt.Candidates.NativeMemChain
open ZkFormal.Near.Render
variable (slot : Nat→Nat)

def lb (k : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => if slot b = k then b + 1 else lb k b

theorem lb_le (k : Nat) : ∀ b, lb slot k b ≤ b
  | 0 => Nat.le_refl _
  | b + 1 => by
    simp only [lb]; split
    · omega
    · have := lb_le k b; omega

theorem lb_ge (k : Nat) {r : Nat} (hr : slot r = k) : ∀ b, r < b → r + 1 ≤ lb slot k b
  | 0, h => absurd h (by omega)
  | b + 1, h => by
    simp only [lb]; split
    · omega
    · rename_i hb
      have : r ≠ b := fun h' => hb (h' ▸ hr)
      exact lb_ge k hr b (by omega)

theorem lb_cases (k : Nat) : ∀ b, lb slot k b = 0 ∨ ∃ r, r < b ∧ slot r = k ∧ lb slot k b = r + 1
  | 0 => Or.inl rfl
  | b + 1 => by
    simp only [lb]; split
    · exact Or.inr ⟨b, by omega, by assumption, rfl⟩
    · rcases lb_cases k b with h | ⟨r, h1, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨r, by omega, h2, h3⟩

/-- `(k, r + 1)` is read: by the next receipt on `k`, or at the end. -/
theorem next_or_last (k : Nat) {r : Nat} (hr : slot r = k) : ∀ b, r < b →
    (∃ r2, r < r2 ∧ r2 < b ∧ slot r2 = k ∧ lb slot k r2 = r + 1) ∨ lb slot k b = r + 1
  | 0, h => absurd h (by omega)
  | b + 1, h => by
    by_cases hb : r = b
    · subst hb; right; simp [lb, hr]
    · rcases next_or_last k hr b (by omega) with ⟨r2, h1, h2, h3, h4⟩ | h'
      · exact Or.inl ⟨r2, h1, by omega, h3, h4⟩
      · by_cases hs : slot b = k
        · exact Or.inl ⟨b, by omega, by omega, hs, h'⟩
        · right; simp only [lb, hs, if_false]; exact h'

/-- `(k, 0)` is read: by the first receipt on `k`, or at the end. -/
theorem first_or_last (k : Nat) : ∀ b,
    (∃ r2, r2 < b ∧ slot r2 = k ∧ lb slot k r2 = 0) ∨ lb slot k b = 0
  | 0 => Or.inr rfl
  | b + 1 => by
    rcases first_or_last k b with ⟨r2, h1, h2, h3⟩ | h'
    · exact Or.inl ⟨r2, by omega, h2, h3⟩
    · by_cases hs : slot b = k
      · exact Or.inl ⟨b, by omega, hs, h'⟩
      · right; simp only [lb, hs, if_false]; exact h'

variable (n : Nat)

/-- Write pairs `(slot, time)` and read pairs. -/
def pairsW (T : List Nat) : List (Nat × Nat) :=
  (List.range n).map (fun r => (slot r, r + 1)) ++ T.map (fun k => (k, 0))
def pairsR (T : List Nat) : List (Nat × Nat) :=
  (List.range n).map (fun r => (slot r, lb slot (slot r) r)) ++
    T.map (fun k => (k, lb slot k n))

theorem pairs_perm {T : List Nat} (hT : T.Nodup) (hs : ∀ r, r < n → slot r ∈ T) :
    (pairsW slot n T).Perm (pairsR slot n T) := by
  have n1 : (pairsW slot n T).Nodup := by
    unfold pairsW
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · apply nodup_map_on _ List.nodup_range
      intro a _ b _ h; simp at h; omega
    · apply nodup_map_on _ hT
      intro a _ b _ h; simp at h; exact h
    · intro x hx y hy
      simp only [List.mem_map, List.mem_range] at hx hy
      obtain ⟨r, _, rfl⟩ := hx; obtain ⟨k, _, rfl⟩ := hy
      intro h; simp at h
  have n2 : (pairsR slot n T).Nodup := by
    unfold pairsR
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · apply nodup_map_on _ List.nodup_range
      intro a ha b hb h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have ha' := List.mem_range.1 ha; have hb' := List.mem_range.1 hb
      rcases Nat.lt_trichotomy a b with hab | hab | hab
      · have := lb_ge slot (slot b) h1 b hab; have := lb_le slot (slot a) a; omega
      · exact hab
      · have := lb_ge slot (slot a) h1.symm a hab; have := lb_le slot (slot b) b; omega
    · apply nodup_map_on _ hT
      intro a _ b _ h; simp at h; exact h.1
    · intro x hx y hy
      simp only [List.mem_map, List.mem_range] at hx hy
      obtain ⟨r, hr, rfl⟩ := hx; obtain ⟨k, _, rfl⟩ := hy
      intro h; simp only [Prod.mk.injEq] at h
      have := lb_ge slot k h.1 _ hr; have := lb_le slot (slot r) r; omega
  rw [List.perm_ext_iff_of_nodup n1 n2]
  rintro ⟨k, t⟩
  simp only [pairsW, pairsR, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro (⟨r, hr, h1, h2⟩ | ⟨k', hk, h1, h2⟩)
    · subst h1 h2
      rcases next_or_last slot (slot r) rfl n hr with ⟨r2, h1, h2, h3, h4⟩ | h
      · exact Or.inl ⟨r2, h2, h3, by rw [h3]; exact h4⟩
      · exact Or.inr ⟨slot r, hs r hr, rfl, h⟩
    · subst h1 h2
      rcases first_or_last slot k' n with ⟨r2, h1, h2, h3⟩ | h
      · exact Or.inl ⟨r2, h1, h2, by rw [h2]; exact h3⟩
      · exact Or.inr ⟨k', hk, rfl, h⟩
  · rintro (⟨r, hr, h1, h2⟩ | ⟨k', hk, h1, h2⟩)
    · subst h1 h2
      rcases lb_cases slot (slot r) r with h | ⟨r', h1, h2, h3⟩
      · exact Or.inr ⟨slot r, hs r hr, rfl, h.symm⟩
      · exact Or.inl ⟨r', by omega, h2, h3.symm⟩
    · subst h1 h2
      rcases lb_cases slot k' n with h | ⟨r', h1, h2, h3⟩
      · exact Or.inr ⟨k', hk, rfl, h.symm⟩
      · exact Or.inl ⟨r', h1, h2, h3.symm⟩


end ZkFormal.NearV3.Rcpt.Candidates.NativeMemChain
