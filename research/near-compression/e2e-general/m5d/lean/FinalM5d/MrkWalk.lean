import NearSpec.Outcome

/-!
# FinalM5d.MrkWalk — the `MRK` level walk computes nearcore's `merklize` root (record level)

The `MRK` table walks a tree level by level: at a level of `c` nodes, row `idx < ⌈c/2⌉` is a hash
row (`2·idx + 1 < c`: node `idx` of the next level is `sha256(N[2idx] ‖ N[2idx+1])`) or, for odd
`c`, the carry row (`2·idx + 1 = c`: the node moves up unhashed); the next level has `⌈c/2⌉`
nodes (`2·c' = c + kc`); a level of one node ends in the terminal row (its node is the root), a
level of zero nodes in the zero hash (`e0`).

* `walkLevel_eq`: one level of the walk is `NearSpec.merkleLevel`;
* `walkRoot_eq`: the walk's root is `NearSpec.merkleRoot` (`merkleFold` with fuel `|leaves|`).

The table-level step (each `MRK` row reads the nodes the previous level wrote: the `NODE` bus is
functional on `(tree, level, index)`) is open; this file fixes what the rows must compute.
-/

namespace FinalM5d.MrkWalk

open NearSpec

/-- One level of the walk: hash rows and (odd `c`) the carry row. -/
def walkLevel (l : List Bytes) : List Bytes :=
  (List.range ((l.length + 1) / 2)).map fun idx =>
    if 2 * idx + 1 < l.length then sha256 (l.getD (2 * idx) [] ++ l.getD (2 * idx + 1) [])
    else l.getD (2 * idx) []

theorem range_succ_map {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl

theorem walkLevel_eq : ∀ l : List Bytes, walkLevel l = merkleLevel l
  | [] => rfl
  | [a] => by simp [walkLevel, merkleLevel]
  | a :: b :: rest => by
    have ih := walkLevel_eq rest
    unfold walkLevel at ih ⊢
    rw [show ((a :: b :: rest).length + 1) / 2 = (rest.length + 1) / 2 + 1 by
      simp only [List.length_cons]; omega, range_succ_map]
    simp only [merkleLevel, List.length_cons, List.getD_cons_zero, List.getD_cons_succ,
      show 2 * 0 + 1 = 1 from rfl, show 2 * 0 = 0 from rfl]
    rw [if_pos (show 1 < rest.length + 1 + 1 by omega)]
    congr 1
    rw [← ih]
    apply List.map_congr_left
    intro i _
    have g : ∀ j, (a :: b :: rest).getD (j + 2) [] = rest.getD j [] := fun j => rfl
    have g2 : ∀ j, (b :: rest).getD (j + 1) [] = rest.getD j [] := fun j => rfl
    have e1 : 2 * (i + 1) = 2 * i + 2 := by omega
    simp only [e1, g, g2]
    by_cases h : 2 * i + 1 < rest.length
    · simp only [show 2 * i + 1 + 2 < rest.length + 1 + 1 from by omega, h, ite_true]
    · simp only [show ¬ (2 * i + 1 + 2 < rest.length + 1 + 1) from by omega, h, ite_false]

theorem walkLevel_length (l : List Bytes) : (walkLevel l).length = (l.length + 1) / 2 := by
  simp [walkLevel]

/-- The walk to the root: levels until one node (the terminal row) or none (the zero hash). -/
def walkRoot (l : List Bytes) : Bytes :=
  match l with
  | [] => zeroHash
  | [x] => x
  | a :: b :: rest => walkRoot (walkLevel (a :: b :: rest))
termination_by l.length
decreasing_by rw [walkLevel_length]; simp only [List.length_cons]; omega

theorem merkleLevel_length_lt : ∀ (a b : Bytes) (rest : List Bytes),
    (merkleLevel (a :: b :: rest)).length < (a :: b :: rest).length := by
  intro a b rest
  rw [← walkLevel_eq, walkLevel_length]; simp only [List.length_cons]; omega

theorem merkleFold_succ2 (n : Nat) (a b : Bytes) (rest : List Bytes) :
    merkleFold (n + 1) (a :: b :: rest) = merkleFold n (merkleLevel (a :: b :: rest)) := by
  rw [merkleFold] <;> simp

/-- `merkleFold` with enough fuel is the walk's root. -/
theorem fold_eq : ∀ (n : Nat) (l : List Bytes), l.length ≤ n → merkleFold n l = walkRoot l
  | _, [], _ => by simp [merkleFold, walkRoot]
  | n, [x], _ => by cases n <;> simp [merkleFold, walkRoot]
  | 0, _ :: _ :: _, h => by simp at h
  | n + 1, a :: b :: rest, h => by
    rw [merkleFold_succ2, walkRoot, walkLevel_eq]
    apply fold_eq
    have := merkleLevel_length_lt a b rest
    simp only [List.length_cons] at h this ⊢; omega

/-- **The walk's root is nearcore's `merklize` root.** -/
theorem walkRoot_eq (l : List Bytes) : walkRoot l = merkleRoot l :=
  (fold_eq l.length l (Nat.le_refl _)).symm

end FinalM5d.MrkWalk
