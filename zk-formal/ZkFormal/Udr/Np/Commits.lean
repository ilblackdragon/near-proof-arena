import ZkFormal.Udr.Np.Late

/-!
# ZkFormal.Udr.Np.Commits — structure of the committed FRI layers

`friCommits` lists `(c_k, a_k)`: layer `c_0 = 0`, `c_{k+1} = c_k + a_k`,
`1 ≤ a_k ≤ max maxArityLog 1`, strictly increasing layers below `ℓ`, no
roll-in strictly inside `(c_k, c_k + a_k)`, and (with enough fuel) the last
commit ends at `ℓ`.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

section
variable (A : Air) (prm : Params) (hdr : List Nat)

theorem cand_sorted (c n : Nat) : ((List.range n).map (fun x => c + 1 + x)).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp (fun h => by omega)

/-- One step of `friCommits.go`. -/
theorem go_step (ℓ c fuel : Nat) (hc : c < ℓ) :
    ∃ nxt, c < nxt ∧ nxt ≤ ℓ ∧ nxt - c ≤ max prm.maxArityLog 1 ∧
      (∀ i, c < i → i < nxt → rollInAt A prm hdr i = false) ∧
      (nxt = ℓ ∨ rollInAt A prm hdr nxt = true ∨ nxt = c + max prm.maxArityLog 1) ∧
      friCommits.go A prm hdr ℓ c (fuel + 1) = (c, nxt - c) :: friCommits.go A prm hdr ℓ nxt fuel := by
  rw [friCommits.go, if_neg (by omega)]
  simp only
  generalize hf : List.find? (fun i => rollInAt A prm hdr i) ((List.range prm.maxArityLog).map (fun x => c + 1 + x)) = r
  rcases r with _ | i0
  · refine ⟨min (c + max prm.maxArityLog 1) ℓ, by omega, by omega, by omega, ?_, by omega, rfl⟩
    intro i h1 h2
    have hn := List.find?_eq_none.mp hf i (List.mem_map.mpr ⟨i - c - 1, List.mem_range.mpr (by
      have := Nat.le_max_left prm.maxArityLog 1
      by_cases hm : prm.maxArityLog = 0
      · rw [hm] at h2; simp at h2; omega
      · rw [Nat.max_eq_left (by omega)] at h2; omega), by omega⟩)
    simpa using hn
  · have hmem := List.mem_of_find?_eq_some hf
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    have ht' := List.mem_range.mp ht
    have hp := List.find?_some hf
    refine ⟨min (c + 1 + t) ℓ, by omega, by omega, by
      have := Nat.le_max_left prm.maxArityLog 1; omega, ?_, ?_, rfl⟩
    · intro i h1 h2
      obtain ⟨-, as, bs, heq, has⟩ := List.find?_eq_some_iff_append.mp hf
      have hi : i ∈ (List.range prm.maxArityLog).map (fun x => c + 1 + x) :=
        List.mem_map.mpr ⟨i - c - 1, List.mem_range.mpr (by omega), by omega⟩
      rw [heq] at hi
      have hs := cand_sorted c prm.maxArityLog
      rw [heq, List.pairwise_append] at hs
      rcases List.mem_append.mp hi with hi | hi
      · simpa using has i hi
      · rcases List.mem_cons.mp hi with hi | hi
        · omega
        · have := (List.pairwise_cons.mp hs.2.1).1 i hi; omega
    · by_cases h : c + 1 + t ≤ ℓ
      · right; left; rw [Nat.min_eq_left h]; simpa using hp
      · left; omega

/-- Elements of `go ℓ c fuel`. -/
theorem go_mem (ℓ : Nat) : ∀ fuel c x, x ∈ friCommits.go A prm hdr ℓ c fuel →
    c ≤ x.1 ∧ x.1 < ℓ ∧ 1 ≤ x.2 ∧ x.1 + x.2 ≤ ℓ
  | 0, c, x, h => by simp [friCommits.go] at h
  | fuel + 1, c, x, h => by
    by_cases hc : c < ℓ
    · obtain ⟨nxt, h1, h2, -, -, -, he⟩ := go_step A prm hdr ℓ c fuel hc
      rw [he] at h
      rcases List.mem_cons.mp h with rfl | h
      · simp; omega
      · have := go_mem ℓ fuel nxt x h; omega
    · rw [friCommits.go, if_pos (by omega)] at h; simp at h

theorem go_sorted (ℓ : Nat) : ∀ fuel c, (friCommits.go A prm hdr ℓ c fuel).Pairwise (fun x y => x.1 < y.1)
  | 0, c => by simp [friCommits.go]
  | fuel + 1, c => by
    by_cases hc : c < ℓ
    · obtain ⟨nxt, h1, h2, -, -, -, he⟩ := go_step A prm hdr ℓ c fuel hc
      rw [he, List.pairwise_cons]
      exact ⟨fun y hy => by have := go_mem A prm hdr ℓ fuel nxt y hy; simp; omega, go_sorted ℓ fuel nxt⟩
    · rw [friCommits.go, if_pos (by omega)]; simp

theorem commits_mem (x : Nat × Nat) (h : x ∈ friCommits A prm hdr) :
    x.1 < finalLayer A prm hdr ∧ 1 ≤ x.2 ∧ x.1 + x.2 ≤ finalLayer A prm hdr := by
  have := go_mem A prm hdr _ _ _ x h; omega

theorem commits_sorted : (friCommits A prm hdr).Pairwise (fun x y => x.1 < y.1) :=
  go_sorted A prm hdr _ _ _

end
end ZkFormal.Udr.Np
