import WasmBase.Main.RowIf
import WasmBase.Main.Lookups
/-!
# WasmBase.Main.RowIfSound — the `IF` row's plumbing against `wasmBaseIfAir`

`Main/RowIf.lean` supplies the *decidable* half of the `IF` table: the CH filter, the record, the
consumed condition, the produced-nothing fact.  This module adds the **plumbing** that makes those
usable against `Holds (wasmBaseIfAir …)`: the 23-table split and the occurrence inclusion.

## The structural obstacle

Every base row lemma takes `Holds (wasmBaseAir …)` and reads its lookups with `fetch_rec` /
`time_chk`, whose statements are hard-wired to the **22-table** AIR: `table_class` quantifies over
`wasmBaseAir` and the `Looks` facts over its occurrences.  An `IF` row lives in `wasmBaseIfAir`
(23 tables), so its FETCH query and its two R16 time-check queries are occurrences of the *larger*
AIR.  The direction of travel matters and is the whole difficulty:

* `wasmBaseIfAir = wasmBaseAir ++ [IF]`, so every base occurrence **is** an `if`-AIR occurrence
  (`occs_base_sub`, proved here) — the easy direction;
* the converse is false: an `IF` occurrence is not a base occurrence.  But `IF` issues no BYTE or
  FUNC query, and its FETCH/R16 queries are answered by the base `Looks` facts, because those facts
  are statements about the *message content*, not about which table issued it.  So a base `Looks`
  transports to the `if` AIR's queries without needing the converse.

This is why the plumbing is mechanical but real: the transfer needs these facts first, and it needs
the `IF` table's own interaction list to be known to carry no BYTE/FUNC query.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## The 23-table split -/

theorem if_air_len' (nloc ncode : Nat) : (wasmBaseIfAir nloc ncode).tables.length = 23 := by
  simp [wasmBaseIfAir, air_len]

/-- A base-AIR table index is the same table, at the same index, in the `if` AIR. -/
theorem if_air_base (nloc ncode t : Nat) (ht : t < 22) :
    (wasmBaseIfAir nloc ncode).tables[t]'(by rw [if_air_len']; omega) =
      (wasmBaseAir nloc ncode).tables[t]'(by rw [air_len]; exact ht) := by
  unfold wasmBaseIfAir
  rw [List.getElem_append_left (by simp [air_len]; exact ht)]

/-- Table 22 of the `if` AIR is `IF`. -/
theorem if_air_last (nloc ncode : Nat) :
    (wasmBaseIfAir nloc ncode).tables[22]'(by rw [if_air_len']; decide) = IfC.table := by
  unfold wasmBaseIfAir
  rw [List.getElem_append_right (by simp [air_len])]
  rfl

/-- **The table split of `wasmBaseIfAir`.**  A table index below 23 is either a base table at the
same index or the appended `IF` table at 22. -/
theorem if_table_class (nloc ncode t : Nat) (ht : t < 23) :
    ((h : t < 22) → (wasmBaseIfAir nloc ncode).tables[t]'(by rw [if_air_len']; exact ht) =
      (wasmBaseAir nloc ncode).tables[t]'(by rw [air_len]; exact h)) ∧
    (t = 22 → (wasmBaseIfAir nloc ncode).tables[t]'(by rw [if_air_len']; exact ht) = IfC.table) := by
  refine ⟨fun h => ?_, fun h22 => ?_⟩
  · exact if_air_base nloc ncode t h
  · subst h22
    exact if_air_last nloc ncode

/-- **Base occurrences are `if`-AIR occurrences.**  `wasmBaseIfAir` is `wasmBaseAir` with one table
appended, so appending cannot lose an occurrence.  This is the one direction that is free. -/
theorem occs_base_sub {nloc ncode : Nat} {tr : Trace} {pub : List F} {o : Occ}
    (ho : o ∈ occs (wasmBaseAir nloc ncode) tr pub) :
    o ∈ occs (wasmBaseIfAir nloc ncode) tr pub := by
  unfold occs at ho ⊢
  simp only [wasmBaseIfAir, List.zipIdx_append, List.flatMap_append]
  exact List.mem_append_left _ ho

end WasmBase
