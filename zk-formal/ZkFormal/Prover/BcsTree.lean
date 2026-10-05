import ZkFormal.Prover.BcsEval

/-!
# ZkFormal.Prover.BcsTree — the prover's MMCS trees, evaluated

`node H o n k j`: the digest at depth `k`, index `j` of the MMCS tree of depth `n`
of oracle `o` under the pure hash `H` (leaves `WH(LEAF, rows)`, inner nodes
`WH(NODE, u8 (n-k) ‖ l ‖ r ‖ rows)`).  `ev_buildTree`: `buildTree` computes
exactly these digests, level by level (`buildTree_at`, `buildTree_root`).

`parentsOf`: the parent indices of a sorted node frontier (`upBytes`'s second
component), with its order and membership facts.
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]
variable (H : Bytes → Bytes) (o : Oracle F)

/-- Digest at distance `d` from the leaves, index `j`, of the tree of depth `n`. -/
def nodeAt (n : Nat) : Nat → Nat → Bytes
  | 0, j => whp H tagLeaf (rowsBytes (K := K) o n j)
  | d + 1, j => whp H tagNode ((UInt8.ofNat (d + 1) :: nodeAt n d (2 * j)) ++
      nodeAt n d (2 * j + 1) ++ rowsBytes (K := K) o (n - (d + 1)) j)

/-- Digest at depth `k`, index `j`. -/
def node (n k j : Nat) : Bytes := nodeAt (K := K) H o n (n - k) j

/-- The digests of depth `k`. -/
def levelL (n k : Nat) : List Bytes := (List.range (2 ^ k)).map (node (K := K) H o n k)

theorem node_leaf (n j : Nat) : node (K := K) H o n n j = whp H tagLeaf (rowsBytes (K := K) o n j) := by
  simp [node, nodeAt]

theorem node_succ {n k : Nat} (hk : k < n) (j : Nat) :
    node (K := K) H o n k j = whp H tagNode ((UInt8.ofNat (n - k) :: node (K := K) H o n (k + 1) (2 * j)) ++
      node (K := K) H o n (k + 1) (2 * j + 1) ++ rowsBytes (K := K) o k j) := by
  have e : n - k = (n - (k + 1)) + 1 := by omega
  have e2 : n - (n - (k + 1) + 1) = k := by omega
  simp only [node]
  rw [e, nodeAt, e2]

theorem levelL_getD {n k j : Nat} (hj : j < 2 ^ k) :
    (levelL (K := K) H o n k).getD j [] = node (K := K) H o n k j := by
  simp [levelL, hj]

theorem ev_go (n : Nat) : ∀ k, k ≤ n → ∀ acc,
    ev H (buildTree.go (K := K) o n k (levelL (K := K) H o n k) acc) =
      (List.range k).map (levelL (K := K) H o n) ++ acc
  | 0, _, acc => rfl
  | k + 1, hk, acc => by
    simp only [buildTree.go, ev_bind, ev_mapOC, ev_WH]
    have hl : ((List.range (2 ^ k)).map fun j =>
        whp H tagNode ((UInt8.ofNat (n - k) :: (levelL (K := K) H o n (k + 1)).getD (2 * j) []) ++
          (levelL (K := K) H o n (k + 1)).getD (2 * j + 1) [] ++ rowsBytes (K := K) o k j)) =
        levelL (K := K) H o n k := by
      conv => rhs; unfold levelL
      apply List.map_congr_left
      intro j hj
      have hj' : j < 2 ^ k := by simpa using hj
      have h2 : 2 * j + 1 < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      have h1 : 2 * j < 2 ^ (k + 1) := by omega
      rw [levelL_getD H o h1, levelL_getD H o h2]
      exact (node_succ H o (by omega) j).symm
    rw [hl, ev_go n k (by omega), List.range_succ, List.map_append, List.append_assoc]
    rfl

/-- **The built tree**: level `k` of `buildTree o` is `levelL k`, `k ≤ n`. -/
theorem ev_buildTree :
    ev H (buildTree (K := K) o) =
      (List.range (treeLog (shapesOf o) + 1)).map (levelL (K := K) H o (treeLog (shapesOf o))) := by
  simp only [buildTree, ev_bind, ev_mapOC, ev_WH]
  have hl : ((List.range (2 ^ treeLog (shapesOf o))).map fun j =>
      whp H tagLeaf (rowsBytes (K := K) o (treeLog (shapesOf o)) j)) =
      levelL (K := K) H o (treeLog (shapesOf o)) (treeLog (shapesOf o)) := by
    unfold levelL
    apply List.map_congr_left
    intro j _
    rw [node_leaf]
  rw [hl, ev_go H o _ _ (Nat.le_refl _), List.range_succ, List.map_append]
  rfl

theorem buildTree_at {k j : Nat} (hk : k ≤ treeLog (shapesOf o)) (hj : j < 2 ^ k) :
    ((ev H (buildTree (K := K) o)).getD k []).getD j [] =
      node (K := K) H o (treeLog (shapesOf o)) k j := by
  have hk' : k < treeLog (shapesOf o) + 1 := by omega
  have e : ((List.range (treeLog (shapesOf o) + 1)).map
      (levelL (K := K) H o (treeLog (shapesOf o)))).getD k [] =
      levelL (K := K) H o (treeLog (shapesOf o)) k := by
    simp [List.getD_eq_getElem?_getD, hk']
  rw [ev_buildTree, e]
  exact levelL_getD H o hj

theorem buildTree_root :
    rootOf (ev H (buildTree (K := K) o)) = node (K := K) H o (treeLog (shapesOf o)) 0 0 :=
  buildTree_at H o (Nat.zero_le _) (by simp)

end

/-! ## Parent indices of a node frontier -/

/-- Parents of a sorted frontier (as `upBytes` / `mpUp` walk it). -/
def parentsOf : List Nat → List Nat
  | [] => []
  | [x] => [x / 2]
  | x :: x' :: rest =>
    if x % 2 = 0 ∧ x' = x + 1 then x / 2 :: parentsOf rest else x / 2 :: parentsOf (x' :: rest)

theorem upBytes_snd {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]
    (lv : List (List Bytes)) (o : Oracle F) (k : Nat) (cur : List Nat) :
    (upBytes (K := K) lv o k cur).2 = parentsOf cur := by
  induction cur using parentsOf.induct with
  | case1 => simp [upBytes, parentsOf]
  | case2 x => simp [upBytes, parentsOf]
  | case3 x x' rest hc ih => rw [upBytes, parentsOf, ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hc)]; simp [ih]
  | case4 x x' rest hc ih => rw [upBytes, parentsOf, ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hc)]; simp [ih]

theorem mem_parentsOf {p : Nat} : ∀ {cur : List Nat}, p ∈ parentsOf cur → ∃ y ∈ cur, p = y / 2 := by
  intro cur
  induction cur using parentsOf.induct with
  | case1 => simp [parentsOf]
  | case2 x => intro h; simp [parentsOf] at h; exact ⟨x, by simp, h⟩
  | case3 x x' rest hc ih =>
    intro h; rw [parentsOf, ite_eq_left_of_eq_true _ _ (eq_true hc)] at h
    rcases List.mem_cons.mp h with h | h
    · exact ⟨x, by simp, h⟩
    · obtain ⟨y, hy, rfl⟩ := ih h; exact ⟨y, by simp [hy], rfl⟩
  | case4 x x' rest hc ih =>
    intro h; rw [parentsOf, ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    rcases List.mem_cons.mp h with h | h
    · exact ⟨x, by simp, h⟩
    · obtain ⟨y, hy, rfl⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, rfl⟩

theorem parentsOf_mem {y : Nat} : ∀ {cur : List Nat}, y ∈ cur → y / 2 ∈ parentsOf cur := by
  intro cur
  induction cur using parentsOf.induct with
  | case1 => simp
  | case2 x => intro h; simp at h; subst h; simp [parentsOf]
  | case3 x x' rest hc ih =>
    intro h; rw [parentsOf, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    simp only [List.mem_cons] at h
    rcases h with rfl | rfl | h
    · simp
    · simp; omega
    · exact List.mem_cons_of_mem _ (ih h)
  | case4 x x' rest hc ih =>
    intro h; rw [parentsOf, ite_eq_right_of_eq_false _ _ (eq_false hc)]
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem parentsOf_lt {k : Nat} {cur : List Nat} (h : ∀ x ∈ cur, x < 2 ^ (k + 1)) :
    ∀ p ∈ parentsOf cur, p < 2 ^ k := by
  intro p hp
  obtain ⟨y, hy, rfl⟩ := mem_parentsOf hp
  have := h y hy; rw [Nat.pow_succ] at this; omega

theorem parentsOf_ne_nil : ∀ {cur : List Nat}, cur ≠ [] → parentsOf cur ≠ [] := by
  intro cur
  induction cur using parentsOf.induct with
  | case1 => simp
  | case2 x => simp [parentsOf]
  | case3 x x' rest hc _ => intro; rw [parentsOf, ite_eq_left_of_eq_true _ _ (eq_true hc)]; simp
  | case4 x x' rest hc _ => intro; rw [parentsOf, ite_eq_right_of_eq_false _ _ (eq_false hc)]; simp

theorem parentsOf_sorted : ∀ {cur : List Nat}, cur.Pairwise (· < ·) →
    (parentsOf cur).Pairwise (· < ·) := by
  intro cur
  induction cur using parentsOf.induct with
  | case1 => simp [parentsOf]
  | case2 x => simp [parentsOf]
  | case3 x x' rest hc ih =>
    intro h; rw [parentsOf, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    simp only [List.pairwise_cons, List.mem_cons] at h
    refine List.Pairwise.cons (fun p hp => ?_) (ih h.2.2)
    obtain ⟨y, hy, rfl⟩ := mem_parentsOf hp
    have := h.2.1 y hy; omega
  | case4 x x' rest hc ih =>
    intro h; rw [parentsOf, ite_eq_right_of_eq_false _ _ (eq_false hc)]
    have h' := h
    simp only [List.pairwise_cons, List.mem_cons] at h
    refine List.Pairwise.cons (fun p hp => ?_) (ih (List.pairwise_cons.mp h').2)
    obtain ⟨y, hy, rfl⟩ := mem_parentsOf hp
    have h1 := h.1 y (by simp at hy; exact hy)
    have h2 := h.1 x' (Or.inl rfl)
    have h3 : y = x' ∨ x' < y := by
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact Or.inl rfl
      · exact Or.inr (h.2.1 y hy')
    omega

theorem parentsOf_zero {cur : List Nat} (hs : cur.Pairwise (· < ·)) (hne : cur ≠ [])
    (hlt : ∀ x ∈ cur, x < 2 ^ 0) : cur = [0] := by
  match cur, hs with
  | [], _ => exact absurd rfl hne
  | [x], _ => have := hlt x (by simp); simp at this; simp [this]
  | x :: y :: r, hs =>
    have h1 := hlt x (by simp); have h2 := hlt y (by simp)
    have := (List.pairwise_cons.mp hs).1 y (by simp)
    simp at h1 h2; omega

end ZkFormal.Prover
