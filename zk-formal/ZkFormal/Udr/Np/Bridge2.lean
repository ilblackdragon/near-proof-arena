import ZkFormal.Udr.Np.Bridge1

/-!
# ZkFormal.Udr.Np.Bridge2 — the transcript at the query phase

* `friCommits` is a chain `0 = c_0 < c_1 = c_0 + a_0 < … < c_K = ℓ` with no
  roll-in strictly inside a block (`chain_commits`);
* the oracles of a transcript at the query phase: three trace oracles, then
  one oracle per commit with a single matrix of `log = n0 - c - a`
  (`query_oracles`);
* the verifier context's `betas` / `gammas` are the FRI challenges by kind.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

section
variable (A : Air) (prm : Params) (hdr : List Nat)

/-- A chain of commits from layer `c` to layer `ℓ`. -/
def Chain (ℓ : Nat) : Nat → List (Nat × Nat) → Prop
  | c, [] => c = ℓ
  | c, (c', a) :: l => c' = c ∧ 1 ≤ a ∧ (∀ i, c < i → i < c + a → rollInAt A prm hdr i = false) ∧
      Chain ℓ (c + a) l

theorem go_chain (ℓ : Nat) : ∀ fuel c, ℓ - c ≤ fuel → c ≤ ℓ →
    Chain A prm hdr ℓ c (friCommits.go A prm hdr ℓ c fuel)
  | 0, c, h1, h2 => by
    simp only [friCommits.go, Chain]; omega
  | fuel + 1, c, h1, h2 => by
    by_cases hc : c < ℓ
    · obtain ⟨nxt, n1, n2, -, n4, -, he⟩ := go_step A prm hdr ℓ c fuel hc
      rw [he]
      refine ⟨rfl, by omega, fun i a b => n4 i a (by omega), ?_⟩
      rw [show c + (nxt - c) = nxt by omega]
      exact go_chain ℓ fuel nxt (by omega) n2
    · rw [friCommits.go, if_pos (by omega)]; simp only [Chain]; omega

theorem chain_commits : Chain A prm hdr (finalLayer A prm hdr) 0 (friCommits A prm hdr) :=
  go_chain A prm hdr _ _ _ (by omega) (by omega)

/-- Layer of commit `k` in a chain. -/
theorem chain_get (ℓ : Nat) : ∀ (l : List (Nat × Nat)) (c : Nat), Chain A prm hdr ℓ c l →
    ∀ k (hk : k < l.length),
      (l[k]).1 = (if k = 0 then c else (l[k - 1]'(by omega)).1 + (l[k - 1]'(by omega)).2) ∧
      1 ≤ (l[k]).2 ∧
      (∀ i, (l[k]).1 < i → i < (l[k]).1 + (l[k]).2 → rollInAt A prm hdr i = false) ∧
      (l[k]).1 + (l[k]).2 = (if h : k + 1 < l.length then (l[k + 1]).1 else ℓ)
  | [], _, _, k, hk => absurd hk (by simp)
  | (c', a) :: l, c, ⟨h1, h2, h3, h4⟩, 0, _ => by
    subst h1
    refine ⟨by simp, h2, h3, ?_⟩
    rcases l with _ | ⟨⟨c'', a'⟩, l⟩
    · simp only [Chain] at h4; simp [h4]
    · simp only [Chain] at h4; simp [h4.1]
  | (c', a) :: l, c, ⟨h1, h2, h3, h4⟩, k + 1, hk => by
    have ih := chain_get ℓ l (c + a) h4 k (by simp at hk; omega)
    simp only [List.getElem_cons_succ, Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte,
      List.length_cons]
    refine ⟨?_, ih.2.1, ih.2.2.1, ?_⟩
    · rcases k with _ | k
      · simp only [↓reduceIte] at ih; rw [ih.1, h1]; simp
      · rw [ih.1]; simp
    · rw [ih.2.2.2]; simp

/-! ## Commit lookups -/

theorem commits_find (k : Nat) (hk : k < (friCommits A prm hdr).length) :
    (friCommits A prm hdr).zipIdx.find? (fun e => e.1.1 == ((friCommits A prm hdr)[k]).1) =
      some ((friCommits A prm hdr)[k], k) := by
  have hs := List.pairwise_iff_getElem.mp (commits_sorted A prm hdr)
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, k, by simp; exact hk, by simp, fun i hi => ?_⟩
  simp only [List.getElem_zipIdx, Nat.zero_add, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
  have := hs i k (by omega) hk hi
  omega

theorem commits_find_none (i : Nat) (h : ∀ k (hk : k < (friCommits A prm hdr).length),
    ((friCommits A prm hdr)[k]).1 ≠ i) :
    (friCommits A prm hdr).zipIdx.find? (fun e => e.1.1 == i) = none := by
  rw [List.find?_eq_none]
  intro e he
  obtain ⟨⟨c, a⟩, k⟩ := e
  have := List.mem_zipIdx_iff_getElem?.mp he
  simp only at this
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp this
  have := h k hk
  rw [hget] at this
  simpa using this

end

/-! ## FRI challenges in the verifier context -/

theorem lookup_filter_true {β : Type} :
    ∀ (l : List ((Bool × Nat) × β)) (i : Nat),
      ((l.filter (·.1.1)).map fun e => (e.1.2, e.2)).lookup i = l.lookup (true, i)
  | [], _ => rfl
  | ((b, i'), v) :: l, i => by
    cases b with
    | true =>
      simp only [List.filter_cons, ↓reduceIte, List.map_cons, List.lookup]
      by_cases h : i = i'
      · subst h; simp
      · have h1 : (i == i') = false := by simp [h]
        have h2 : ((true, i) == (true, i')) = false := by simp [h]
        rw [h1, h2]; exact lookup_filter_true l i
    | false =>
      simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte, List.lookup]
      have h2 : ((true, i) == (false, i')) = false := by simp
      rw [h2]; exact lookup_filter_true l i

theorem lookup_filter_false {β : Type} :
    ∀ (l : List ((Bool × Nat) × β)) (i : Nat),
      (l.filter (fun e => !e.1.1)).lookup (false, i) = l.lookup (false, i)
  | [], _ => rfl
  | ((b, i'), v) :: l, i => by
    cases b with
    | false =>
      simp only [List.filter_cons, Bool.not_false, ↓reduceIte, List.lookup]
      by_cases h : i = i'
      · subst h; simp
      · have h2 : ((false, i) == (false, i')) = false := by simp [h]
        rw [h2]; exact lookup_filter_false l i
    | true =>
      simp only [List.filter_cons, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.lookup]
      have h2 : ((false, i) == (true, i')) = false := by simp
      rw [h2]; exact lookup_filter_false l i

theorem getD_of_keys {β : Type} [Inhabited β] (d : β) :
    ∀ (n s : Nat) (l : List ((Bool × Nat) × β)), l.map Prod.fst = (List.range' s n).map (fun i => (false, i)) →
      ∀ i, i < n → (l.map Prod.snd).getD i d = (l.lookup (false, s + i)).getD d
  | 0, _, _, _, i, hi => absurd hi (by omega)
  | n + 1, s, [], h, _, _ => by simp [List.range'_succ] at h
  | n + 1, s, (k, v) :: l, h, i, hi => by
    rw [List.range'_succ] at h
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rcases i with _ | i
    · simp [List.lookup]
    · have ih := getD_of_keys d n (s + 1) l h i (by omega)
      simp only [List.map_cons, List.getD_cons_succ, ih, List.lookup]
      have : ((false, s + (i + 1)) == (false, s)) = false := by simp
      rw [this, show s + 1 + i = s + (i + 1) by omega]

theorem kinds_filter_false (A : Air) (prm : Params) (hdr : List Nat) :
    (friChalKinds A prm hdr).filter (fun k => !k.1) =
      (List.range' 0 (finalLayer A prm hdr)).map (fun i => (false, i)) := by
  rw [friChalKinds_eq, List.filter_append, ← List.range_eq_range']
  have h2 : (if rollInAt A prm hdr (finalLayer A prm hdr) then [(true, finalLayer A prm hdr)] else
      ([] : List (Bool × Nat))).filter (fun k => !k.1) = [] := by
    split <;> rfl
  rw [h2, List.append_nil]
  generalize finalLayer A prm hdr = N
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.filter_append, ih, List.map_append,
      List.flatMap_singleton]
    congr 1
    simp only [gK]
    split <;> rfl

end ZkFormal.Udr.Np
