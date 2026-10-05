import ZkFormal.Prover.BcsTree

/-!
# ZkFormal.Prover.BcsMulti — multiproof completeness

For an oracle `o` with well-formed rows and a 32-byte hash `H`, the verifier's
multiproof reader (`mpLeaves`, `mpUp`, `mpLevels`, `multiproof`) run on the
prover's stream `multiproofBytes` (for a sorted, duplicate-free, non-empty set of
leaf indices `S < 2^n`) recomputes the prover's root, consumes exactly the stream,
and opens, at every level `k` that injects matrices, the true rows of every node
on the paths from `S` (`ev_multiproof`).
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]

/-- Every opened entry holds the true rows of its node. -/
def GoodOp (o : Oracle F) (op : Opened F) : Prop := ∀ e ∈ op, e.2 = levelRows o e.1.1 e.1.2

theorem GoodOp.nil (o : Oracle F) : GoodOp o [] := fun _ h => by cases h

theorem GoodOp.append {o : Oracle F} {a b : Opened F} (ha : GoodOp o a) (hb : GoodOp o b) :
    GoodOp o (a ++ b) := fun e he => by
  rcases List.mem_append.mp he with h | h
  · exact ha e h
  · exact hb e h

theorem GoodOp.cons {o : Oracle F} {k j : Nat} {op : Opened F} (h : GoodOp o op) :
    GoodOp o (((k, j), levelRows o k j) :: op) := fun e he => by
  rcases List.mem_cons.mp he with rfl | h'
  · rfl
  · exact h e h'

variable (H : Bytes → Bytes)

theorem ev_mpNode {lvl : Nat} {ws : List Nat} {x : Nat} {lft rgt r : Bytes} {rows : List (List F)}
    {r' : Bytes} (h : readRows (F := F) ws r = some (rows, r')) :
    ev H (mpNode (F := F) lvl ws x lft rgt r) =
      some ((x, whp H tagNode ((UInt8.ofNat lvl :: lft) ++ rgt ++ r.take (r.length - r'.length))),
        (if ws.isEmpty then none else some rows), r') := by
  simp only [mpNode, readInj, h, ev_bind_WH, ev_pure]

variable (o : Oracle F)

theorem node_length (hH : ∀ m, (fit32 (H m)).length = 32) (n k j : Nat) :
    (node (K := K) H o n k j).length = 64 := by
  unfold node
  cases n - k with
  | zero => exact whp_length hH _ _
  | succ d => exact whp_length hH _ _

theorem node_even {n k x : Nat} (hk : k < n) (he : x % 2 = 0) :
    node (K := K) H o n k (x / 2) = whp H tagNode ((UInt8.ofNat (n - k) ::
      node (K := K) H o n (k + 1) x) ++ node (K := K) H o n (k + 1) (x ^^^ 1) ++
        rowsBytes (K := K) o k (x / 2)) := by
  rw [node_succ H o hk, xor_one_even he]
  have : 2 * (x / 2) = x := by omega
  rw [this]

theorem node_odd {n k x : Nat} (hk : k < n) (ho : x % 2 = 1) :
    node (K := K) H o n k (x / 2) = whp H tagNode ((UInt8.ofNat (n - k) ::
      node (K := K) H o n (k + 1) (x ^^^ 1)) ++ node (K := K) H o n (k + 1) x ++
        rowsBytes (K := K) o k (x / 2)) := by
  rw [node_succ H o hk, xor_one_odd ho]
  have h1 : 2 * (x / 2) = x - 1 := by omega
  have h2 : x - 1 + 1 = x := by omega
  rw [h1, h2]

theorem node_pair {n k x : Nat} (hk : k < n) (he : x % 2 = 0) :
    node (K := K) H o n k (x / 2) = whp H tagNode ((UInt8.ofNat (n - k) ::
      node (K := K) H o n (k + 1) x) ++ node (K := K) H o n (k + 1) (x + 1) ++
        rowsBytes (K := K) o k (x / 2)) := by
  rw [node_even H o hk he, xor_one_even he]

theorem optCons (ws : List Nat) (k j : Nat) (op : Opened F) (hop : GoodOp o op) :
    GoodOp o (match (if ws.isEmpty = true then none else some (levelRows o k j)) with
      | some rows => ((k, j), rows) :: op
      | none => op) ∧
    (ws ≠ [] → ((k, j), levelRows o k j) ∈ (match (if ws.isEmpty = true then none else
      some (levelRows o k j)) with
      | some rows => ((k, j), rows) :: op
      | none => op)) ∧
    (∀ e ∈ op, e ∈ (match (if ws.isEmpty = true then none else some (levelRows o k j)) with
      | some rows => ((k, j), rows) :: op
      | none => op)) := by
  cases hw : ws.isEmpty
  · simp only [Bool.false_eq_true, ite_false]
    exact ⟨hop.cons, fun _ => by simp, fun e he => List.mem_cons_of_mem _ he⟩
  · simp only [ite_true]
    refine ⟨hop, fun h => absurd (List.isEmpty_iff.mp hw) h, fun e he => he⟩

/-- Known nodes of depth `k`. -/
def nodesOf (n k : Nat) (cur : List Nat) : List (Nat × Bytes) :=
  cur.map fun j => (j, node (K := K) H o n k j)

theorem ev_mpUp_nil (k lvl : Nat) (ws : List Nat) (r : Bytes) :
    ev H (mpUp (F := F) k lvl ws [] r) = some ([], [], r) := by
  simp only [mpUp, ev_pure]

/-- **One level of a multiproof.** -/
theorem ev_mpUp (hH : ∀ m, (fit32 (H m)).length = 32) (hr : RowsOk o) {k : Nat}
    (hk : k < treeLog (shapesOf o)) (rest : Bytes) : ∀ cur : List Nat, (∀ x ∈ cur, x < 2 ^ (k + 1)) →
    ∃ op, ev H (mpUp (F := F) k (treeLog (shapesOf o) - k) (levelWidths (shapesOf o) k)
        (nodesOf (K := K) H o (treeLog (shapesOf o)) (k + 1) cur)
        ((upBytes (K := K) (ev H (buildTree (K := K) o)) o k cur).1 ++ rest)) =
      some (nodesOf (K := K) H o (treeLog (shapesOf o)) k (parentsOf cur), op, rest) ∧ GoodOp o op ∧
      (levelWidths (shapesOf o) k ≠ [] → ∀ x ∈ cur, ((k, x / 2), levelRows o k (x / 2)) ∈ op) := by
  intro cur
  induction cur using parentsOf.induct with
  | case1 =>
    intro _
    exact ⟨[], by simp [upBytes, parentsOf, nodesOf, ev_mpUp_nil], GoodOp.nil o, by simp⟩
  | case2 x =>
    intro hlt
    have hx := hlt x (by simp)
    have hsib := buildTree_at (K := K) H o (k := k + 1) (by omega) (xor_one_lt hx)
    have hp : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    have hrr := readRows_rowsBytes (K := K) o hr k (x / 2) hp rest
    have ht : take? 64 (node (K := K) H o (treeLog (shapesOf o)) (k + 1) (x ^^^ 1) ++
        (rowsBytes (K := K) o k (x / 2) ++ rest)) =
        some (node (K := K) H o (treeLog (shapesOf o)) (k + 1) (x ^^^ 1),
          rowsBytes (K := K) o k (x / 2) ++ rest) := by
      rw [← node_length H o hH (treeLog (shapesOf o)) (k + 1) (x ^^^ 1)]; exact take?_append _ _
    simp only [upBytes, hsib, parentsOf, nodesOf, List.map_cons, List.map_nil, List.append_assoc]
    rcases Nat.mod_two_eq_zero_or_one x with he | ho
    · simp only [mpUp, ht, he, ite_true, ev_bind, ev_mpNode H hrr, take_consumed, ev_pure]
      rw [← node_even H o hk he]
      obtain ⟨h1, h2, _⟩ := optCons o (levelWidths (shapesOf o) k) k (x / 2) [] (GoodOp.nil o)
      exact ⟨_, rfl, h1, fun hw y hy => by simp at hy; subst hy; exact h2 hw⟩
    · have hne : ¬ (x % 2 = 0) := by omega
      simp only [mpUp, ht, hne, ite_false, ev_bind, ev_mpNode H hrr, take_consumed, ev_pure]
      rw [← node_odd H o hk ho]
      obtain ⟨h1, h2, _⟩ := optCons o (levelWidths (shapesOf o) k) k (x / 2) [] (GoodOp.nil o)
      exact ⟨_, rfl, h1, fun hw y hy => by simp at hy; subst hy; exact h2 hw⟩
  | case3 x x' rest' hc ih =>
    intro hlt
    obtain ⟨he, rfl⟩ := hc
    have hx := hlt x (by simp)
    have hp : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    obtain ⟨op', hev, hgood, hcov⟩ := ih fun y hy => hlt y (by simp [hy])
    have hrr := readRows_rowsBytes (K := K) o hr k (x / 2) hp
      ((upBytes (K := K) (ev H (buildTree (K := K) o)) o k rest').1 ++ rest)
    have hc' : x % 2 = 0 ∧ x + 1 = x + 1 := ⟨he, rfl⟩
    rw [upBytes, ite_eq_left_of_eq_true _ _ (eq_true hc'), parentsOf,
      ite_eq_left_of_eq_true _ _ (eq_true hc')]
    simp only [nodesOf, List.map_cons, List.append_assoc]
    simp only [nodesOf] at hev
    simp only [mpUp, he, true_and, ite_true, ev_bind, ev_mpNode H hrr, take_consumed, ev_pure, hev]
    rw [← node_pair H o hk he]
    obtain ⟨h1, h2, h3⟩ := optCons o (levelWidths (shapesOf o) k) k (x / 2) op' hgood
    refine ⟨_, rfl, h1, fun hw y hy => ?_⟩
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · exact h2 hw
    · have : (x + 1) / 2 = x / 2 := by omega
      rw [this]; exact h2 hw
    · exact h3 _ (hcov hw y hy)
  | case4 x x' rest' hc ih =>
    intro hlt
    have hx := hlt x (by simp)
    have hp : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    obtain ⟨op', hev, hgood, hcov⟩ := ih fun y hy => hlt y (List.mem_cons_of_mem _ hy)
    have hsib := buildTree_at (K := K) H o (k := k + 1) (by omega) (xor_one_lt hx)
    have hrr := readRows_rowsBytes (K := K) o hr k (x / 2) hp
      ((upBytes (K := K) (ev H (buildTree (K := K) o)) o k (x' :: rest')).1 ++ rest)
    rw [upBytes, ite_eq_right_of_eq_false _ _ (eq_false hc), parentsOf,
      ite_eq_right_of_eq_false _ _ (eq_false hc)]
    simp only [hsib, nodesOf, List.map_cons, List.append_assoc]
    simp only [nodesOf, List.map_cons] at hev
    have ht := take?_append (node (K := K) H o (treeLog (shapesOf o)) (k + 1) (x ^^^ 1))
      (rowsBytes (K := K) o k (x / 2) ++
        ((upBytes (K := K) (ev H (buildTree (K := K) o)) o k (x' :: rest')).1 ++ rest))
    rw [node_length H o hH] at ht
    rcases Nat.mod_two_eq_zero_or_one x with he | ho
    · have hx' : ¬ x' = x + 1 := fun h => hc ⟨he, h⟩
      simp only [mpUp, he, hx', and_false, ite_false, ht, ite_true, ev_bind, ev_mpNode H hrr,
        take_consumed, ev_pure, hev]
      rw [← node_even H o hk he]
      obtain ⟨h1, h2, h3⟩ := optCons o (levelWidths (shapesOf o) k) k (x / 2) op' hgood
      refine ⟨_, rfl, h1, fun hw y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h2 hw
      · exact h3 _ (hcov hw y hy)
    · have hne : ¬ (x % 2 = 0) := by omega
      simp only [mpUp, hne, false_and, ite_false, ht, ev_bind, ev_mpNode H hrr, take_consumed,
        ev_pure, hev]
      rw [← node_odd H o hk ho]
      obtain ⟨h1, h2, h3⟩ := optCons o (levelWidths (shapesOf o) k) k (x / 2) op' hgood
      refine ⟨_, rfl, h1, fun hw y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h2 hw
      · exact h3 _ (hcov hw y hy)

theorem ev_mpLeaves (hr : RowsOk o) : ∀ (S : List Nat), (∀ s ∈ S, s < 2 ^ treeLog (shapesOf o)) →
    ∀ rest : Bytes,
    ev H (mpLeaves (F := F) (treeLog (shapesOf o)) (levelWidths (shapesOf o) (treeLog (shapesOf o))) S
        (S.flatMap (rowsBytes (K := K) o (treeLog (shapesOf o))) ++ rest)) =
      some (nodesOf (K := K) H o (treeLog (shapesOf o)) (treeLog (shapesOf o)) S,
        S.map (fun j => ((treeLog (shapesOf o), j), levelRows o (treeLog (shapesOf o)) j)), rest)
  | [], _, rest => by simp [mpLeaves, nodesOf, ev_pure]
  | x :: S, hlt, rest => by
    have hrr := readRows_rowsBytes (K := K) o hr _ x (hlt x (by simp))
      (S.flatMap (rowsBytes (K := K) o (treeLog (shapesOf o))) ++ rest)
    have ih := ev_mpLeaves hr S (fun s hs => hlt s (by simp [hs])) rest
    simp only [mpLeaves, List.flatMap_cons, List.append_assoc, hrr, take_consumed, ev_bind,
      ih, ev_pure, ev_WH, nodesOf, List.map_cons, node_leaf]

theorem shiftRight_one (x : Nat) : x >>> 1 = x / 2 := by
  rw [Nat.shiftRight_eq_div_pow]

theorem ev_mpLevels (hH : ∀ m, (fit32 (H m)).length = 32) (hr : RowsOk o) :
    ∀ k, k ≤ treeLog (shapesOf o) → ∀ cur : List Nat, cur.Pairwise (· < ·) → cur ≠ [] →
    (∀ x ∈ cur, x < 2 ^ k) → ∀ rest : Bytes,
    ∃ op, ev H (mpLevels (F := F) (shapesOf o) (treeLog (shapesOf o)) k
        (nodesOf (K := K) H o (treeLog (shapesOf o)) k cur)
        (levelsBytes (K := K) (ev H (buildTree (K := K) o)) o k cur ++ rest)) =
      some (node (K := K) H o (treeLog (shapesOf o)) 0 0, op, rest) ∧ GoodOp o op ∧
      ∀ k' < k, levelWidths (shapesOf o) k' ≠ [] → ∀ x ∈ cur,
        ((k', x >>> (k - k')), levelRows o k' (x >>> (k - k'))) ∈ op
  | 0, _, cur, hs, hne, hlt, rest => by
    rw [parentsOf_zero hs hne hlt]
    refine ⟨[], ?_, GoodOp.nil o, fun k' hk' => absurd hk' (Nat.not_lt_zero _)⟩
    simp [nodesOf, mpLevels, levelsBytes, ev_pure]
  | k + 1, hk, cur, hs, hne, hlt, rest => by
    obtain ⟨op1, hev1, hg1, hc1⟩ := ev_mpUp H o hH hr (k := k) (by omega)
      (levelsBytes (K := K) (ev H (buildTree (K := K) o)) o k
        (parentsOf cur) ++ rest) cur hlt
    obtain ⟨op2, hev2, hg2, hc2⟩ := ev_mpLevels hH hr k (by omega) (parentsOf cur)
      (parentsOf_sorted hs) (parentsOf_ne_nil hne) (parentsOf_lt hlt) rest
    refine ⟨op1 ++ op2, ?_, hg1.append hg2, ?_⟩
    · simp only [mpLevels, levelsBytes, upBytes_snd, List.append_assoc] at hev1 ⊢
      simp only [ev_bind, hev1, hev2, ev_pure]
    · intro k' hk' hw x hx
      by_cases hkk : k' = k
      · subst hkk
        have : k' + 1 - k' = 1 := by omega
        rw [this, shiftRight_one]
        exact List.mem_append_left _ (hc1 hw x hx)
      · have h := hc2 k' (by omega) hw (x / 2) (parentsOf_mem hx)
        have e : x >>> (k + 1 - k') = (x / 2) >>> (k - k') := by
          rw [← shiftRight_one, ← Nat.shiftRight_add]; congr 1; omega
        rw [e]
        exact List.mem_append_right _ h

/-- **Multiproof completeness** for one oracle. -/
theorem ev_multiproof (hH : ∀ m, (fit32 (H m)).length = 32) (hr : RowsOk o) (S : List Nat)
    (hs : S.Pairwise (· < ·)) (hne : S ≠ []) (hlt : ∀ s ∈ S, s < 2 ^ treeLog (shapesOf o))
    (rest : Bytes) :
    ∃ op, ev H (multiproof (F := F) (shapesOf o) (rootOf (ev H (buildTree (K := K) o))) S
        (multiproofBytes (K := K) (ev H (buildTree (K := K) o)) o S ++ rest)) = some (op, rest) ∧
      GoodOp o op ∧ ∀ k ≤ treeLog (shapesOf o), levelWidths (shapesOf o) k ≠ [] → ∀ s ∈ S,
        ((k, s >>> (treeLog (shapesOf o) - k)),
          levelRows o k (s >>> (treeLog (shapesOf o) - k))) ∈ op := by
  obtain ⟨op2, hev2, hg2, hc2⟩ := ev_mpLevels H o hH hr _ (Nat.le_refl _) S hs hne hlt rest
  refine ⟨S.map (fun j => ((treeLog (shapesOf o), j), levelRows o (treeLog (shapesOf o)) j)) ++ op2,
    ?_, ?_, ?_⟩
  · have e : ((shapesOf o).map (·.1)).foldr max 0 = treeLog (shapesOf o) := rfl
    simp only [multiproof, multiproofBytes, e, List.append_assoc, ev_bind,
      ev_mpLeaves H o hr S hlt, hev2, ev_pure, buildTree_root, beq_self_eq_true, ite_true]
  · refine GoodOp.append (fun e he => ?_) hg2
    simp only [List.mem_map] at he
    obtain ⟨j, _, rfl⟩ := he
    rfl
  · intro k hk hw s hsS
    by_cases hkn : k = treeLog (shapesOf o)
    · subst hkn
      simp only [Nat.sub_self, Nat.shiftRight_zero]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨s, hsS, rfl⟩)
    · exact List.mem_append_right _ (hc2 k (by omega) hw s hsS)

end

end ZkFormal.Prover
