import NearSpecV3.Wasm.TrieAccounting

/-!
# `w.size`: is `Σ|values| + 2000·R` an upper bound on the chunk's recorded storage?

Answer to `UQ-015` / inventory row `L0-D2-040` (owner L5), against the pinned nearcore
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`.

## What nearcore actually computes

`Trie::recorded_storage_size_upper_bound` (`core/store/src/trie/mod.rs:696-700`) reads
`TrieRecorder::upper_bound_size`, which is maintained by three increments only
(`core/store/src/trie/trie_recording.rs:15-37`):

* `record_with` (:115-132): `+= serialized.len()` for a hash **the first time it is inserted**
  (`size_from_first_insert`), so the sum is over *distinct* recorded hashes;
* `record_key_removal` (:140-146): `+= 2000` per `TrieUpdate::remove` of a
  `TrieKey::ContractData` (`core/store/src/trie/update.rs:169-181`);
* `record_code_len` (:148-159): `+= code_len`. **At this commit it has no caller**: `git grep`
  finds only the definition and the `TrieRecorderStats` field, and `codes_to_record`
  (`:37`, read at `trie/mod.rs:1592-1598`) is never inserted into. So this term is `0` here.

So, writing `R` for the number of contract-data removals charged during the main transition,

  `recorded_storage_size_upper_bound = (Σ_{h ∈ recorded, distinct} |bytes h|) + 2000·R + 0`.

The Lean guard is `baseBytes + 2000 * out.cdRemovals ≤ 4 000 000`
(`NearSpecV3/ChunkValidationD2.lean:235-237`) with `baseBytes = Σ |w.main.values ++ codes|`.
Both limits are the same number at PV86: `main_storage_proof_size_soft_limit = 4_000_000`
(`core/parameters/res/runtime_configs/72.yaml:1`) and `per_receipt_storage_proof_size_limit =
4_000_000` (`69.yaml:5`), confirmed in `parameters.snap:11-12`.

## What this module proves, and what it does not

`Rec` below is exactly the above counter. Theorems:

* `Rec.size_le_recorded` — the upper bound is at most `Σ|values| + 2000·R + code` **given**
  `List.Sublist r.charged values`, i.e. every recorded item is one of the witness's base-state
  values. That inclusion is a nearcore-level fact (the validator's trie is
  `Trie::from_recorded_storage(base_state, root)` — `trie/mod.rs:715-735`, reached from
  `chunk_validation.rs:432-435` — so a recorded hash can only be a value that was in
  `base_state`), and is therefore a **hypothesis here, not a theorem**.

Three caveats on that hypothesis, all checked at the pinned commit and all *not* proved:

1. The inclusion must hold for the *validator's* trie, which uses `from_recorded_storage` and no
   memtrie; the memtrie path (`mem/iter.rs:44`, `mem/memtrie_update.rs:117`) re-serialises nodes
   and would need the serialisation to agree, and `record_unaccounted`
   (`trie/mod.rs:757-770`) is `test_features`-only.
2. `removals` must count every `TrieUpdate::remove` of a `ContractData` key in the main
   transition. There are exactly two live sites: `runtime/runtime/src/ext.rs:258`
   (`storage_remove`, replayed by `D3/FunctionCall.lean:311-316`) and
   `runtime/runtime/src/actions.rs:406` → `core/store/src/utils/mod.rs:549` (`DeleteAccount`,
   modelled by `D2/Actions.lean:241-242`). `TrieKey::ContractData` is column `9`
   (`core/primitives/src/trie_key.rs:50`), which is the test `Ovl.remove` applies
   (`D2/State.lean:117-120`). Every other `state_update.remove` in `runtime/` targets a different
   column (columns 3,4,5,6,10-12,13,14,20,22,23 and access keys) and charges nothing.
3. `w.size` bounds only the *main* transition. Each implicit transition is a separate
   `apply_chunk` with its own recorder and its own 4 MB limit (`chunk_validation.rs:678-692` →
   `runtime/mod.rs:1257-1258`), and `checkD2Core` applies no size bound to
   `w.implicit`/`T.implicit` at all. That is a second, independent hole in the guard's coverage
   of the chunk: it is not about the inequality being false, it is about the inequality being
   stated for the wrong trie.
* `Rec.size_record_ge` / `Rec.size_removal_ge` — `upper_bound_size` only grows, so a bound at the
  end of the transition bounds it at every earlier point (the limit is tested with `>` after every
  op: `recorded_storage_counter.rs:19-33`).
* `guard_sufficient` — the Lean guard, with the same hypothesis, implies the limit is never
  exceeded. **This is the soundness claim of `L0-D2-040`, and it holds.**
* `removal_charge_can_exceed_limit` — `2000·2001 = 4 002 000 > 4 000 000`: the removal charge is
  load-bearing, so the `2000·R` term cannot be dropped.
* `per_receipt_limit_does_not_bound_chunk` — two operations each within the per-receipt limit can
  exceed the chunk limit, so the chunk guard is **not** derivable from the per-receipt limit.

## Why the guard is nevertheless the wrong boundary

The chunk-level limit is a *soft* limit: when `check_proof_size_limit_exceed` becomes true the
runtime does not reject the chunk, it stops processing receipts and defers the rest
(`runtime/runtime/src/lib.rs:2386, 2464, 2576, 3003, 2703`;
`congestion_control.rs:889`), and nearcore's own documentation says a valid chunk's proof may
reach ~8 MB ("the total size of storage proof could reach 8 MB (3.99MB + one receipt which
generates 4MB)", `docs/misc/state_witness_size_limits.md`). A protocol-valid chunk can therefore
have `recorded_storage_size_upper_bound > 4 000 000`, so `w.size` excludes protocol-valid cases
rather than describing a boundary. The real per-receipt boundary is also not a *validity*
condition: exceeding `per_receipt_storage_proof_size_limit` makes that receipt fail with
`RecordedStorageExceeded` (`runtime/near-vm-runner/src/logic/recorded_storage_counter.rs:19-33`,
`logic/errors.rs:357`), it does not invalidate the chunk. Faithful semantics therefore need a
chunk-scoped recorder plus soft-limit deferral, which is successor-relation work (L1), not a
change to this module or to the current checker.
-/

namespace NearSpecV3.StorageBound

/-- `main_storage_proof_size_soft_limit` at PV86 (`runtime_configs/72.yaml:1`). -/
def softLimit : Nat := 4000000

/-- `per_receipt_storage_proof_size_limit` at PV86 (`runtime_configs/69.yaml:5`). -/
def perReceiptLimit : Nat := 4000000

/-- The two protocol limits are the same number at the pinned commit. -/
theorem limits_eq : softLimit = perReceiptLimit := rfl

/-- The Lean `D3` per-receipt constant is the same number (`Wasm/TrieAccounting.lean:153`). -/
theorem perReceiptLimit_eq_lean :
    NearSpecV3.Wasm.TTN.perReceiptProofLimit = perReceiptLimit := rfl

/-! ## Arithmetic -/

/-- Left-fold sum, matching `baseBytes = (merged.map List.length).foldl (· + ·) 0`
(`ChunkValidationD2.lean:234-235`). -/
def sumN : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumN xs

theorem sumN_append (a b : List Nat) : sumN (a ++ b) = sumN a + sumN b := by
  induction a with
  | nil => simp [sumN]
  | cons x xs ih => simp only [List.cons_append, sumN, ih]; omega

theorem sumN_le_of_sublist {a b : List Nat} (h : List.Sublist a b) : sumN a ≤ sumN b := by
  induction h with
  | slnil => simp [sumN]
  | cons _ _ ih => simp only [sumN]; omega
  | cons_cons _ ih => simp only [sumN]; omega

/-! ## The recorder -/

/-- `TrieRecorder`'s proof-size counter (`trie/trie_recording.rs:15-37`): the `(hash, size)`
pairs charged so far, the number of charged contract-data removals, and the charged code bytes.

`charged` is a list rather than a map so the model stays structural; `record` enforces the
"first insertion only" rule of `record_with`, so every hash appears at most once. -/
structure Rec where
  charged : List (Nat × Nat) := []
  removals : Nat := 0
  codeBytes : Nat := 0

namespace Rec

/-- `TrieRecorder::record_with`: charge a hash's serialized length only on first insertion. -/
def record (r : Rec) (h n : Nat) : Rec :=
  if (r.charged.map (fun p => p.1)).contains h then r
  else { r with charged := r.charged ++ [(h, n)] }

/-- `TrieRecorder::record_key_removal`: `+= 2000` per contract-data removal. -/
def removal (r : Rec) : Rec := { r with removals := r.removals + 1 }

/-- `upper_bound_size`. -/
def size (r : Rec) : Nat := sumN (r.charged.map (fun p => p.2)) + 2000 * r.removals + r.codeBytes

theorem size_record_ge (r : Rec) (h n : Nat) : r.size ≤ (r.record h n).size := by
  unfold record
  split
  · exact Nat.le_refl r.size
  · simp only [size, List.map_append, List.map_cons, List.map_nil, sumN_append, sumN]
    omega

theorem size_removal_ge (r : Rec) : r.size ≤ r.removal.size := by
  simp only [removal, size]; omega

/-- **The upper-bound step.** If every charged item is one of the base-state values, the
recorder's size is at most the base-state byte total plus the removal and code charges. -/
theorem size_le_recorded {r : Rec} {values : List (Nat × Nat)}
    (h : List.Sublist r.charged values) :
    r.size ≤ sumN (values.map (fun p => p.2)) + 2000 * r.removals + r.codeBytes := by
  have hm : List.Sublist (r.charged.map (fun p => p.2)) (values.map (fun p => p.2)) := h.map _
  have hsum : sumN (r.charged.map (fun p => p.2)) ≤ sumN (values.map (fun p => p.2)) :=
    sumN_le_of_sublist hm
  simp only [size]; omega

/-- **The soundness claim of `L0-D2-040`.** With the same inclusion hypothesis, the Lean guard
`Σ|values| + 2000·R ≤ 4 000 000` implies the chunk's `recorded_storage_size_upper_bound` never
exceeds the soft limit. -/
theorem guard_sufficient {r : Rec} {values : List (Nat × Nat)}
    (h : List.Sublist r.charged values)
    (hguard : sumN (values.map (fun p => p.2)) + 2000 * r.removals + r.codeBytes ≤ softLimit) :
    r.size ≤ softLimit :=
  Nat.le_trans (size_le_recorded h) hguard

end Rec

/-! ## The removal charge is load-bearing -/

/-- `2 001` charged contract-data removals already cost `4 002 000` bytes, above the limit, with no
values recorded at all. So the `2000·R` term cannot be dropped from the guard. -/
theorem removal_charge_can_exceed_limit :
    ∃ r : Rec, r.charged = [] ∧ r.removals = 2001 ∧ r.size > softLimit :=
  ⟨⟨[], 2001, 0⟩, rfl, rfl, by decide⟩

/-! ## The per-receipt limit does not give the chunk bound -/

/-- Two receipts can each be within `per_receipt_storage_proof_size_limit` and still exceed the
chunk's soft limit (the documented `3.99MB + 4MB ≈ 8MB` case). Hence the chunk-level guard is not
implied by the per-receipt limit: it has to be stated and enforced separately, as
`ChunkValidationD2.lean:235-237` does. -/
theorem per_receipt_limit_does_not_bound_chunk :
    ∃ a b : Nat, a ≤ perReceiptLimit ∧ b ≤ perReceiptLimit ∧ softLimit < a + b :=
  ⟨2500000, 2500000, by decide, by decide, by decide⟩

end NearSpecV3.StorageBound
