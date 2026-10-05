import ZkFormal.Near.Render.Proof.BusCommon
import ZkFormal.Near.Spec.SoundAccount

/-!
# ZkFormal.Near.Render.Proof.MemChain — memory timestamps of a batch

`lb e k b`: one plus the last receipt `< b` on slot `k` (`0` if none);
`tprevOf e r = lb e (slot r) r`, `tlastOf e k = lb e k n`.  The write
times `{0} ∪ {r + 1 | slot r = k}` and the read times `{tprev r | slot r = k}
∪ {tlast k}` of a slot are the same set (`pairs_perm`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

namespace MemChain
variable (e : Ext)

def lb (k : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => if e.slot b = k then b + 1 else lb k b

theorem lb_filter (k : Nat) (p : Nat → Bool) (hp : ∀ r, p r = decide (e.slot r = k)) : ∀ b,
    (((List.range b).filter p).getLast?.map (· + 1)).getD 0 = lb e k b
  | 0 => rfl
  | b + 1 => by
    rw [List.range_succ, List.filter_append, lb, ← lb_filter k p hp b]
    by_cases h : e.slot b = k
    · simp [List.filter_cons, hp, h]
    · simp [List.filter_cons, hp, h]

theorem tprev_eq (r : Nat) : tprevOf e r = lb e (e.slot r) r :=
  lb_filter e _ _ (fun _ => rfl) r

theorem tlast_eq (k : Nat) : tlastOf e k = lb e k e.rs.length :=
  lb_filter e _ _ (fun _ => rfl) _

theorem lb_le (k : Nat) : ∀ b, lb e k b ≤ b
  | 0 => Nat.le_refl _
  | b + 1 => by
    simp only [lb]; split
    · omega
    · have := lb_le k b; omega

theorem lb_ge (k : Nat) {r : Nat} (hr : e.slot r = k) : ∀ b, r < b → r + 1 ≤ lb e k b
  | 0, h => absurd h (by omega)
  | b + 1, h => by
    simp only [lb]; split
    · omega
    · rename_i hb
      have : r ≠ b := fun h' => hb (h' ▸ hr)
      exact lb_ge k hr b (by omega)

theorem lb_cases (k : Nat) : ∀ b, lb e k b = 0 ∨ ∃ r, r < b ∧ e.slot r = k ∧ lb e k b = r + 1
  | 0 => Or.inl rfl
  | b + 1 => by
    simp only [lb]; split
    · exact Or.inr ⟨b, by omega, by assumption, rfl⟩
    · rcases lb_cases k b with h | ⟨r, h1, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨r, by omega, h2, h3⟩

theorem amt_lb (k : Nat) : ∀ b, e.amtAt k b = e.amtAt k (lb e k b)
  | 0 => rfl
  | b + 1 => by
    simp only [lb]; split
    · rfl
    · rename_i h; simp only [Ext.amtAt, h, if_false, Nat.add_zero]; exact amt_lb k b

/-- `(k, r + 1)` is read: by the next receipt on `k`, or at the end. -/
theorem next_or_last (k : Nat) {r : Nat} (hr : e.slot r = k) : ∀ b, r < b →
    (∃ r2, r < r2 ∧ r2 < b ∧ e.slot r2 = k ∧ lb e k r2 = r + 1) ∨ lb e k b = r + 1
  | 0, h => absurd h (by omega)
  | b + 1, h => by
    by_cases hb : r = b
    · subst hb; right; simp [lb, hr]
    · rcases next_or_last k hr b (by omega) with ⟨r2, h1, h2, h3, h4⟩ | h'
      · exact Or.inl ⟨r2, h1, by omega, h3, h4⟩
      · by_cases hs : e.slot b = k
        · exact Or.inl ⟨b, by omega, by omega, hs, h'⟩
        · right; simp only [lb, hs, if_false]; exact h'

/-- `(k, 0)` is read: by the first receipt on `k`, or at the end. -/
theorem first_or_last (k : Nat) : ∀ b,
    (∃ r2, r2 < b ∧ e.slot r2 = k ∧ lb e k r2 = 0) ∨ lb e k b = 0
  | 0 => Or.inr rfl
  | b + 1 => by
    rcases first_or_last k b with ⟨r2, h1, h2, h3⟩ | h'
    · exact Or.inl ⟨r2, by omega, h2, h3⟩
    · by_cases hs : e.slot b = k
      · exact Or.inl ⟨b, by omega, hs, h'⟩
      · right; simp only [lb, hs, if_false]; exact h'

/-- Write pairs `(slot, time)` and read pairs. -/
def pairsW (T : List Nat) : List (Nat × Nat) :=
  (List.range e.rs.length).map (fun r => (e.slot r, r + 1)) ++ T.map (fun k => (k, 0))
def pairsR (T : List Nat) : List (Nat × Nat) :=
  (List.range e.rs.length).map (fun r => (e.slot r, lb e (e.slot r) r)) ++
    T.map (fun k => (k, lb e k e.rs.length))

theorem pairs_perm {T : List Nat} (hT : T.Nodup) (hs : ∀ r, r < e.rs.length → e.slot r ∈ T) :
    (pairsW e T).Perm (pairsR e T) := by
  have n1 : (pairsW e T).Nodup := by
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
  have n2 : (pairsR e T).Nodup := by
    unfold pairsR
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · apply nodup_map_on _ List.nodup_range
      intro a ha b hb h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have ha' := List.mem_range.1 ha; have hb' := List.mem_range.1 hb
      rcases Nat.lt_trichotomy a b with hab | hab | hab
      · have := lb_ge e (e.slot b) h1 b hab; have := lb_le e (e.slot a) a; omega
      · exact hab
      · have := lb_ge e (e.slot a) h1.symm a hab; have := lb_le e (e.slot b) b; omega
    · apply nodup_map_on _ hT
      intro a _ b _ h; simp at h; exact h.1
    · intro x hx y hy
      simp only [List.mem_map, List.mem_range] at hx hy
      obtain ⟨r, hr, rfl⟩ := hx; obtain ⟨k, _, rfl⟩ := hy
      intro h; simp only [Prod.mk.injEq] at h
      have := lb_ge e k h.1 _ hr; have := lb_le e (e.slot r) r; omega
  rw [List.perm_ext_iff_of_nodup n1 n2]
  rintro ⟨k, t⟩
  simp only [pairsW, pairsR, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro (⟨r, hr, h1, h2⟩ | ⟨k', hk, h1, h2⟩)
    · subst h1 h2
      rcases next_or_last e (e.slot r) rfl e.rs.length hr with ⟨r2, h1, h2, h3, h4⟩ | h
      · exact Or.inl ⟨r2, h2, h3, by rw [h3]; exact h4⟩
      · exact Or.inr ⟨e.slot r, hs r hr, rfl, h⟩
    · subst h1 h2
      rcases first_or_last e k' e.rs.length with ⟨r2, h1, h2, h3⟩ | h
      · exact Or.inl ⟨r2, h1, h2, by rw [h2]; exact h3⟩
      · exact Or.inr ⟨k', hk, rfl, h⟩
  · rintro (⟨r, hr, h1, h2⟩ | ⟨k', hk, h1, h2⟩)
    · subst h1 h2
      rcases lb_cases e (e.slot r) r with h | ⟨r', h1, h2, h3⟩
      · exact Or.inr ⟨e.slot r, hs r hr, rfl, h.symm⟩
      · exact Or.inl ⟨r', by omega, h2, h3.symm⟩
    · subst h1 h2
      rcases lb_cases e k' e.rs.length with h | ⟨r', h1, h2, h3⟩
      · exact Or.inr ⟨k', hk, rfl, h.symm⟩
      · exact Or.inl ⟨r', h1, h2, h3.symm⟩

end MemChain

end ZkFormal.Near.Render
