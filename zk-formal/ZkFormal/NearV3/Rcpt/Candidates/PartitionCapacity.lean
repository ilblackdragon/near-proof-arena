import ZkFormal.NearV3.Rcpt.Candidates.SourceBudget

/-! Placement lemmas for the isolated two-log23 candidate. These prove list/capacity
facts only, not the AIR continuation or cross-partition bus contracts. -/
namespace ZkFormal.NearV3.Rcpt.Candidates

/-- Split before one carried row: the left trace reserves its last physical row for
an authenticated copy of the right trace's first row. -/
def splitTrace {α : Type} (cap : Nat) (xs : List α) : List α × List α :=
  if xs.length ≤ cap then (xs, []) else (xs.take (cap - 1), xs.drop (cap - 1))

def leftTrace {α : Type} (cap : Nat) (xs : List α) : List α :=
  let p := splitTrace cap xs
  p.1 ++ p.2.head?.toList

theorem splitTrace_reconstruct {α : Type} (cap : Nat) (xs : List α) :
    (splitTrace cap xs).1 ++ (splitTrace cap xs).2 = xs := by
  unfold splitTrace
  split
  · simp
  · exact List.take_append_drop _ xs

/-- An overlap costs at most one physical row, while preserving every logical row. -/
theorem splitTrace_capacity {α : Type} (cap : Nat) (xs : List α)
    (hcap : 0 < cap) (hsize : xs.length ≤ 2 * cap - 1) :
    (leftTrace cap xs).length ≤ cap ∧ (splitTrace cap xs).2.length ≤ cap := by
  unfold leftTrace splitTrace
  split
  · rename_i h
    simpa using h
  · have hh : (xs.drop (cap - 1)).head?.toList.length ≤ 1 := by
      cases (xs.drop (cap - 1)).head? <;> simp
    simp only [List.length_append, List.length_take, List.length_drop]
    omega

/-- The actual dedup source envelope fits two physical log23 traces including overlap. -/
theorem source_partition_capacity {α : Type} (xs : List α) (h : xs.length ≤ 16334272) :
    (leftTrace (2 ^ 23) xs).length ≤ 2 ^ 23 ∧
      (splitTrace (2 ^ 23) xs).2.length ≤ 2 ^ 23 :=
  splitTrace_capacity _ xs (by decide) (by omega)

/-- Greedy whole-message split; no SHA message is divided between partitions. -/
def splitBudget : Nat → List Nat → List Nat × List Nat
  | _, [] => ([], [])
  | cap, a :: rest =>
    if a ≤ cap then
      let p := splitBudget (cap - a) rest
      (a :: p.1, p.2)
    else ([], a :: rest)

theorem splitBudget_reconstruct (cap : Nat) (xs : List Nat) :
    (splitBudget cap xs).1 ++ (splitBudget cap xs).2 = xs := by
  induction xs generalizing cap with
  | nil => rfl
  | cons a rest ih =>
    unfold splitBudget
    split
    · simp only [List.cons_append, ih]
    · rfl

theorem splitBudget_prefix_le (cap : Nat) (xs : List Nat) :
    (splitBudget cap xs).1.sum ≤ cap := by
  induction xs generalizing cap with
  | nil => simp [splitBudget]
  | cons a rest ih =>
    unfold splitBudget
    split
    · rename_i ha
      have hh := ih (cap - a)
      simp only [List.sum_cons]
      omega
    · simp

theorem splitBudget_stop (cap : Nat) (xs : List Nat) {a : Nat} {rest : List Nat}
    (h : (splitBudget cap xs).2 = a :: rest) :
    cap < (splitBudget cap xs).1.sum + a := by
  induction xs generalizing cap with
  | nil => cases h
  | cons b tail ih =>
    unfold splitBudget at h ⊢
    by_cases hb : b ≤ cap
    · simp only [if_pos hb] at h ⊢
      have hh := ih (cap - b) h
      simp only [List.sum_cons]
      omega
    · simp only [if_neg hb] at h ⊢
      cases h
      simp only [List.sum_nil, Nat.zero_add]
      omega

/-- Total budget plus one largest message suffices for two whole-message partitions. -/
theorem splitBudget_capacity (cap maxMessage : Nat) (xs : List Nat)
    (hm : ∀ a ∈ xs, a ≤ maxMessage) (hcap : maxMessage ≤ cap)
    (htotal : xs.sum + maxMessage ≤ 2 * cap) :
    (splitBudget cap xs).1.sum ≤ cap ∧ (splitBudget cap xs).2.sum ≤ cap := by
  refine ⟨splitBudget_prefix_le cap xs, ?_⟩
  have hj := splitBudget_reconstruct cap xs
  have hsum := congrArg List.sum hj
  simp only [List.sum_append] at hsum
  cases hr : (splitBudget cap xs).2 with
  | nil => simp
  | cons a rest =>
    have hstop := splitBudget_stop cap xs hr
    have ha : a ∈ xs := by rw [← hj, hr]; simp
    have hma := hm a ha
    rw [hr] at hsum
    simp only [List.sum_cons] at hsum ⊢
    omega

/-- All source SHA messages have 18 or35 rows, so the source-only budget packs without splitting. -/
theorem source_sha_partition_capacity (weights : List Nat)
    (hm : ∀ a ∈ weights, a ≤ 35) (htotal : weights.sum ≤ 8932712) :
    (splitBudget (2 ^ 23) weights).1.sum ≤ 2 ^ 23 ∧
      (splitBudget (2 ^ 23) weights).2.sum ≤ 2 ^ 23 :=
  splitBudget_capacity _ 35 weights hm (by decide) (by omega)

/-- The global source+receipt+trie envelope also packs when every message has at most
2,228,242 rows (the bound for an 8 MiB preimage). The preimage premise remains explicit. -/
theorem global_sha_partition_capacity (weights : List Nat)
    (hm : ∀ a ∈ weights, a ≤ 2228242) (htotal : weights.sum ≤ 12674664) :
    (splitBudget (2 ^ 23) weights).1.sum ≤ 2 ^ 23 ∧
      (splitBudget (2 ^ 23) weights).2.sum ≤ 2 ^ 23 :=
  splitBudget_capacity _ 2228242 weights hm (by decide) (by omega)

theorem bounded_preimage_rows (len : Nat) (h : len ≤ witnessBytes) :
    msgRows len ≤ 2228242 := by
  simp only [msgRows, witnessBytes] at *
  omega

end ZkFormal.NearV3.Rcpt.Candidates
