import ZkFormal.V2.PG.NpBasic

/-!
# ZkFormal.V2.PG.NpCommits (P2 copy of `Prover.NpCommits` at `dp = pg g`) — the committed FRI layers form a chain `0 = c₀ < c₁ < … < ℓ`

`friCommits` returns `(c_k, a_k)` with `c_{k+1} = c_k + a_k`, `a_k ≥ 1`, ending at `ℓ`, and
no roll-in strictly inside a step (`Chain`).  Consequences: the fold kinds' messages carry
exactly the committed oracles in order (`filterMap_range_lookup`), and every roll-in layer
`0 < i < ℓ` starts a commitment.
-/

namespace ZkFormal.V2.PG

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.Prover ZkFormal.Prover.Np

/-- `l` is a commitment chain from `c` to `ℓ` avoiding roll-ins (`R`) strictly inside steps. -/
def Chain (R : Nat → Bool) (ℓ : Nat) : Nat → List (Nat × Nat) → Prop
  | c, [] => ℓ ≤ c
  | c, (c', a) :: l => c' = c ∧ 1 ≤ a ∧ c + a ≤ ℓ ∧ (∀ i, c < i → i < c + a → R i = false) ∧
      Chain R ℓ (c + a) l

theorem chain_go (A : Air) (prm : Params) (hdr : List Nat) (hm : 1 ≤ prm.maxArityLog) :
    ∀ fuel c, finalLayer A prm hdr ≤ c + fuel →
      Chain (rollInAt A prm hdr) (finalLayer A prm hdr) c
        (friCommits.go A prm hdr (finalLayer A prm hdr) c fuel) := by
  intro fuel
  induction fuel with
  | zero => intro c h; simp only [friCommits.go]; show _ ≤ c; omega
  | succ fuel ih =>
    intro c h
    simp only [friCommits.go]
    split
    · assumption
    · rename_i hlt
      suffices H : ∀ nxt, (c < nxt ∧ nxt ≤ finalLayer A prm hdr ∧
          ∀ i, c < i → i < nxt → rollInAt A prm hdr i = false) →
          Chain (rollInAt A prm hdr) (finalLayer A prm hdr) c
            ((c, nxt - c) :: friCommits.go A prm hdr (finalLayer A prm hdr) nxt fuel) by
        apply H
        split
        · rename_i i hf
          have hmem := List.mem_of_find?_eq_some hf
          simp only [List.mem_map, List.mem_range] at hmem
          obtain ⟨m, hm', rfl⟩ := hmem
          refine ⟨Nat.lt_min.mpr ⟨by omega, by omega⟩, Nat.min_le_right _ _, fun j h1 h2 => ?_⟩
          have h2' : j < c + 1 + m := Nat.lt_of_lt_of_le h2 (Nat.min_le_left _ _)
          rw [List.find?_eq_some_iff_getElem] at hf
          obtain ⟨_, idx, hidx, hget, hprev⟩ := hf
          simp only [List.getElem_map, List.getElem_range] at hget
          have := hprev (j - c - 1) (by omega)
          simp only [List.getElem_map, List.getElem_range] at this
          rw [show c + 1 + (j - c - 1) = j by omega] at this
          simpa using this
        · rename_i hf
          have hmx : max prm.maxArityLog 1 = prm.maxArityLog := Nat.max_eq_left hm
          refine ⟨Nat.lt_min.mpr ⟨by omega, by omega⟩, Nat.min_le_right _ _, fun j h1 h2 => ?_⟩
          have h2' : j < c + max prm.maxArityLog 1 := Nat.lt_of_lt_of_le h2 (Nat.min_le_left _ _)
          have := List.find?_eq_none.mp hf j (by
            simp only [List.mem_map, List.mem_range]; exact ⟨j - c - 1, by omega, by omega⟩)
          simpa using this
      intro nxt ⟨k1, k2, k3⟩
      refine ⟨rfl, by omega, by omega, fun i h1 h2 => k3 i h1 (by omega), ?_⟩
      rw [show c + (nxt - c) = nxt by omega]
      exact ih nxt (by omega)

theorem commits_chain (A : Air) (tr : Trace Fp) :
    Chain (rollInAt A dp (hdr A tr)) (ell A tr) 0 (commits A tr) := by
  unfold commits friCommits ell
  exact chain_go A dp (hdr A tr) (by dp_decide) _ 0 (by omega)

theorem chain_keys_ge {R : Nat → Bool} {ℓ : Nat} : ∀ {c : Nat} {l : List (Nat × Nat)},
    Chain R ℓ c l → ∀ p ∈ l, c ≤ p.1
  | _, [], _, p, hp => by simp at hp
  | c, (c', a) :: l, ⟨h1, h2, _, _, h5⟩, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [h1]
    · have := chain_keys_ge h5 p hp; omega

theorem lookup_none_of_lt {l : List (Nat × Nat)} {i : Nat} (h : ∀ p ∈ l, i < p.1) :
    l.lookup i = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨c, a⟩ := p
    have hc := h (c, a) (by simp)
    simp only at hc
    have : (i == c) = false := by simp; omega
    simp only [List.lookup, this]
    exact ih fun q hq => h q (by simp [hq])

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (by simp),
      filterMap_congr' (fun b hb => h b (by simp [hb]))]

/-- Lookups along the layers of a chain enumerate it in order. -/
theorem filterMap_range_lookup {β : Type} {R : Nat → Bool} {ℓ : Nat} (f : Nat → Nat → β) :
    ∀ {c : Nat} {l : List (Nat × Nat)}, Chain R ℓ c l →
      (List.range' c (ℓ - c)).filterMap (fun i => (l.lookup i).map (f i)) = l.map fun p => f p.1 p.2
  | c, [], h => by
    have : ℓ - c = 0 := by simp only [Chain] at h; omega
    rw [this]; rfl
  | c, (c', a) :: l, ⟨h1, h2, h3, _, h5⟩ => by
    subst h1
    have hk := chain_keys_ge h5
    have hsplit : List.range' c' (ℓ - c') = List.range' c' a ++ List.range' (c' + a) (ℓ - (c' + a)) := by
      have := (List.range'_append_1 (s := c') (m := a) (n := ℓ - (c' + a)))
      rw [this]; congr 1; omega
    have hl : ∀ i, i ≠ c' → ((c', a) :: l).lookup i = l.lookup i := by
      intro i hi
      have : (i == c') = false := by simp [hi]
      simp only [List.lookup, this]
    have e1 : (List.range' c' a).filterMap (fun i => (((c', a) :: l).lookup i).map (f i)) =
        [f c' a] := by
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [List.range'_succ, List.filterMap_cons]
      simp only [List.lookup, beq_self_eq_true, Option.map_some]
      congr 1
      rw [List.filterMap_eq_nil_iff]
      intro i hi
      rw [List.mem_range'_1] at hi
      have := hl i (by omega)
      simp only [List.lookup] at this
      rw [this, lookup_none_of_lt (fun p hp => by have := hk p hp; omega)]
      rfl
    have e2 : (List.range' (c' + a) (ℓ - (c' + a))).filterMap
        (fun i => (((c', a) :: l).lookup i).map (f i)) =
        (List.range' (c' + a) (ℓ - (c' + a))).filterMap (fun i => (l.lookup i).map (f i)) := by
      apply filterMap_congr'
      intro i hi
      rw [List.mem_range'_1] at hi
      rw [hl i (by omega)]
    rw [hsplit, List.filterMap_append, e1, e2, filterMap_range_lookup f h5]
    rfl

end ZkFormal.V2.PG
