import StateM5a.StateViewParams
import NearSpecV3.E2E.Glue

/-!
# Lane E's STATE glue against lane B's working set (E2E-M12, item 2)

M12's `Glue.state_glue` needed lane B's side as a functional `ApplyFaithfulS root apply`; that
premise is **retired** (decision D-c, lane B's finding B2-1: a function of the root is not what a
circuit proves) in favour of the relational split (`Glue.split_sound_relC_relOn`, lane B's
`GlueRel.state_sound_relC_rel`, and with `W` = `stRoot` lane E's `join/StateW.lean`). This file
(lane E, outside lane B's directory, like `StViewE.lean`) still records the shape lane B's working
set has, which `GlueRel.entries_updK` uses:

* `entryOf t f k`: lane B's entry `(k, pre, cur, written)` from the trie and the lookup;
  **`entryAt_eq`**: `StateViewParams.entryAt o k = entryOf o.trie (Glue.kv o) k` (definitional);
* `rootB P κ I t f := wsRoot P ((κ I).map (entryOf t f))` (lane B's `RCH` root over the chunk's
  keys); **`wsRoot_entryAt`**: lane B's root of `(κ I).map (entryAt o)` is `rootB P κ I o.trie
  (Glue.kv o)`.

So lane B's relational half for the M12 instance (`GlueRel.StHalfRelS`) is `m5tSeg`'s
`WsBus.seg_root` / `chain_sound` over the entries `(κ I).map (entryOf t f)`.

Check: `cd research/near-compression/e2e-general/m5a/lean && lake env lean ../../join/GlueB.lean`.
Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace LaneE.GlueB

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E StateM5a.StateView StateM5a.StateViewParams

/-- Lane B's working-set entry from a partial trie and a committed lookup. -/
def entryOf (t : PTrie) (f : Bytes → Option (Option Bytes)) (k : Bytes) : Entry :=
  match f k with
  | some x => (k, (t.find (nibbles k)).getD none, x, true)
  | none => (k, (t.find (nibbles k)).getD none, (t.find (nibbles k)).getD none, false)

/-- **Lane B's entry depends on the overlay only through its trie and committed lookups.** -/
theorem entryAt_eq (o : Ovl) (k : Bytes) : entryAt o k = entryOf o.trie (Glue.kv o) k := by
  unfold entryAt entryOf Glue.kv preV
  rfl

/-- Lane B's working-set root over the chunk's keys, from a trie and a committed lookup. -/
def rootB (P : StViewParams) (κ : Intake → List Bytes) (I : Intake) (t : PTrie)
    (f : Bytes → Option (Option Bytes)) : Bytes :=
  wsRoot P ((κ I).map (entryOf t f))

theorem wsRoot_entryAt (P : StViewParams) (κ : Intake → List Bytes) (I : Intake) (o : Ovl) :
    wsRoot P ((κ I).map (entryAt o)) = rootB P κ I o.trie (Glue.kv o) := by
  unfold rootB
  rw [List.map_congr_left fun k _ => entryAt_eq o k]

#print axioms entryAt_eq
#print axioms wsRoot_entryAt

end LaneE.GlueB
