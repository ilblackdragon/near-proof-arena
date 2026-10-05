import ZkFormal.Prover.BcsShape

/-!
# ZkFormal.Prover.BcsEval — deterministic evaluation against a pure hash; codecs

* `ev H oa`: the result of running the query tree `oa` against the pure hash `H`
  (`runH (pureH H)`); `ev_bind`, `ev_WH`, `ev_mapOC` make every component a pure
  function of `H`.
* Codec round trips: canonical base/extension elements (`readFs_enc`, `readKs_enc`),
  the rows injected at a tree level (`readRows_rowsBytes`).
* `xor_one`: the sibling index.
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

/-! ## Evaluation -/

/-- Run a query tree against a pure hash function. -/
def ev {α : Type} (H : Bytes → Bytes) (oa : OracleComp hashSpec α) : α := (runH (pureH H) oa ()).1

theorem ev_pure {α : Type} (H : Bytes → Bytes) (a : α) : ev H (.pure a) = a := rfl

theorem ev_query {α : Type} (H : Bytes → Bytes) (q : Bytes) (k : Bytes → OracleComp hashSpec α) :
    ev H (.query q k) = ev H (k (H q)) := rfl

theorem ev_bind {α β : Type} (H : Bytes → Bytes) (oa : OracleComp hashSpec α)
    (f : α → OracleComp hashSpec β) : ev H (OracleComp.bind oa f) = ev H (f (ev H oa)) := by
  induction oa with
  | pure a => rfl
  | query q k ih => exact ih (H q)

/-- The wide hash as a pure function. -/
def whp (H : Bytes → Bytes) (tag : UInt8) (m : Bytes) : Bytes :=
  fit32 (H (tag :: 1 :: m)) ++ fit32 (H (tag :: 2 :: m))

theorem ev_WH (H : Bytes → Bytes) (tag : UInt8) (m : Bytes) : ev H (WH tag m) = whp H tag m := rfl

theorem ev_H (H' : Bytes → Bytes) (m : Bytes) : ev H' (Stark.H m) = fit32 (H' m) := rfl

theorem ev_bind_WH {β : Type} (H : Bytes → Bytes) (tag : UInt8) (m : Bytes)
    (f : Bytes → OracleComp hashSpec β) :
    ev H (OracleComp.bind (WH tag m) f) = ev H (f (whp H tag m)) := by
  rw [ev_bind, ev_WH]

theorem ev_mapOC {α β : Type} (H : Bytes → Bytes) (f : α → OracleComp hashSpec β) :
    ∀ l : List α, ev H (mapOC f l) = l.map fun a => ev H (f a)
  | [] => rfl
  | a :: as => by
    simp only [mapOC, ev_bind, ev_mapOC H f as, ev_pure, List.map_cons]

/-- Wide hashes are 64 bytes (answers are normalised by `fit32`). -/
theorem whp_length {H : Bytes → Bytes} (hH : ∀ m, (fit32 (H m)).length = 32) (tag : UInt8) (m : Bytes) :
    (whp H tag m).length = 64 := by
  simp [whp, hH]

/-! ## Sibling index -/

theorem xor_one_div (x : Nat) : (x ^^^ 1) / 2 = x / 2 := by
  rw [Nat.xor_div_two]; simp

theorem xor_one_mod (x : Nat) : (x ^^^ 1) % 2 = 1 - x % 2 := by
  have h := @Nat.xor_mod_two_eq_one x 1
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (x ^^^ 1) with hy | hy <;> simp [hx, hy] at h ⊢

theorem xor_one_even {x : Nat} (h : x % 2 = 0) : x ^^^ 1 = x + 1 := by
  have h1 := xor_one_div x; have h2 := xor_one_mod x
  have := Nat.div_add_mod (x ^^^ 1) 2; have := Nat.div_add_mod x 2
  omega

theorem xor_one_odd {x : Nat} (h : x % 2 = 1) : x ^^^ 1 = x - 1 := by
  have h1 := xor_one_div x; have h2 := xor_one_mod x
  have := Nat.div_add_mod (x ^^^ 1) 2; have := Nat.div_add_mod x 2
  omega

theorem xor_one_lt {x k : Nat} (h : x < 2 ^ (k + 1)) : x ^^^ 1 < 2 ^ (k + 1) :=
  Nat.xor_lt_two_pow h (Nat.one_lt_two_pow (by omega))

/-! ## Codecs -/

theorem take?_append (a b : Bytes) : take? a.length (a ++ b) = some (a, b) := by
  simp [take?]

theorem take_consumed (a b : Bytes) : (a ++ b).take ((a ++ b).length - b.length) = a := by
  simp

theorem P_lt : P < 2 ^ 32 := by decide

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]

attribute [local instance] Semiring.natCast

theorem readU32s_enc : ∀ (row : List F) (rest : Bytes),
    readU32s row.length (row.flatMap (encF (K := K)) ++ rest) =
      some (row.map (StarkField.toNat (K := K)), rest)
  | [], rest => rfl
  | a :: row, rest => by
    have hl : (encF (K := K) a).length = 4 := Bytes.leN_length _ _
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readU32s]
    rw [← hl, take?_append]
    simp only [readU32s_enc row rest, List.map_cons, encF]
    rw [leToNat_leN4 _ (Nat.lt_trans (StarkFieldLaws.toNat_lt a) P_lt)]

theorem readFs_enc (row : List F) (rest : Bytes) :
    readFs (F := F) row.length (row.flatMap (encF (K := K)) ++ rest) = some (row, rest) := by
  unfold readFs
  rw [readU32s_enc row rest]
  have hall : (row.map (StarkField.toNat (K := K))).all (· < P) = true := by
    simp only [List.all_map, List.all_eq_true]
    intro a _; simpa using StarkFieldLaws.toNat_lt (K := K) a
  simp only [hall, ite_true, List.map_map]
  congr
  conv => rhs; rw [← List.map_id row]
  apply List.map_congr_left
  intro a _
  exact StarkFieldLaws.natCast_toNat (K := K) a

theorem readKs_enc : ∀ (xs : List K) (rest : Bytes),
    readKs (F := F) xs.length (xs.flatMap (encK (F := F)) ++ rest) = some (xs, rest)
  | [], rest => rfl
  | x :: xs, rest => by
    have hl : (StarkField.limbs x : List F).length = 8 := StarkFieldLaws.limbs_length x
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readKs, encK]
    rw [← hl, readFs_enc]
    simp only [readKs_enc xs rest, StarkFieldLaws.ofLimbs_limbs]

/-- Rows of the matrices of level `k` at index `j` (in order). -/
def levelRows (o : Oracle F) (k j : Nat) : List (List F) :=
  (o.filter fun M => M.log == k).map fun M => M.row j

/-- Every row of every matrix has the matrix width. -/
def RowsOk (o : Oracle F) : Prop := ∀ M ∈ o, ∀ i, i < 2 ^ M.log → (M.row i).length = M.width

theorem levelWidths_shapesOf (o : Oracle F) (k : Nat) :
    levelWidths (shapesOf o) k = (o.filter fun M => M.log == k).map (·.width) := by
  induction o with
  | nil => rfl
  | cons M o ih =>
    simp only [shapesOf, List.map_cons, levelWidths, List.filter_cons] at ih ⊢
    split <;> simp_all

theorem readRows_gen : ∀ (ms : List (Mat F)) (j : Nat) (rest : Bytes),
    (∀ M ∈ ms, (M.row j).length = M.width) →
    readRows (F := F) (ms.map (·.width))
      (ms.flatMap (fun M => (M.row j).flatMap (encF (K := K))) ++ rest) =
      some (ms.map fun M => M.row j, rest)
  | [], _, _, _ => rfl
  | M :: ms, j, rest, h => by
    simp only [List.map_cons, List.flatMap_cons, List.append_assoc, readRows]
    rw [← h M (by simp), readFs_enc]
    simp only [readRows_gen ms j rest fun M' hM' => h M' (by simp [hM'])]

theorem readRows_rowsBytes (o : Oracle F) (hr : RowsOk o) (k j : Nat) (hj : j < 2 ^ k)
    (rest : Bytes) :
    readRows (F := F) (levelWidths (shapesOf o) k) (rowsBytes (K := K) o k j ++ rest) =
      some (levelRows o k j, rest) := by
  rw [levelWidths_shapesOf]
  apply readRows_gen
  intro M hM
  simp only [List.mem_filter, beq_iff_eq] at hM
  exact hr M hM.1 j (hM.2 ▸ hj)

end

end ZkFormal.Prover
