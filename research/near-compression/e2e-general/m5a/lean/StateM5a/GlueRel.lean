import StateM5a.StHalfC
import NearSpecV3.E2E.Glue

/-!
# StateM5a.GlueRel — B-T2 against lane E's M12 STATE glue (`NearSpecV3.E2E.Glue`)

Lane E's M12 (merged into this branch) restates lane B's side of the STATE glue as
`Glue.ApplyFaithfulS root apply : ∀ I t f q, apply q (root I t f) = root I t (updK q f)` — the
same functional shape as lane F's `ApplyFaithful`, and unprovable for the same reason
(`StHalfC.applyFaithful_coll`, finding B2-1): a function of the root must send two inputs with one
root (a SHA-384 collision of two entry lists) to one output.

Here lane E's STATE instance (`Glue.stateSem`, `W` = the optional working-set root) is closed with
the **relational** state half instead:

* **`StHalfRelS`** — the state rows move *every* `(trie, lookup)` whose root is the input value to
  the root of the lookup updated by the bus traffic;
* **`state_sound_relC_rel`** — lane F's `EngHalfRCOn` (with `StatePre`) ∧ `StHalfRelS` ⇒
  `TmplSoundRel8C … .state`, through lane E's own `state_reqs` (no `ApplyFaithfulS`);
* **`entries_updK`** — lane B's entries of the updated lookup are `StHalfC.updE` of the entries
  (`GlueB.entryOf` restated as `entryOfT`), so `StHalfRelS` for `root = wsRoot ∘ entries` is
  `WsBridge.WsMoves` with `upd = updE q`.

**Caveat (why lane B's own instance uses `W = stRoot`).** `WsMoves` (what `ws_moves_seg` derives
from `Holds m5tSeg`) holds for entry lists with the leaf's public `wsLen` entries, all values
`< 2^24` bytes. With `W` = the bare working-set root nothing carries `wsLen` or the value bounds,
so `StHalfRelS` for every `(t, f)` is not derivable from the circuit; with `W = stRoot`
(`StHalfC.stHalf_inst`) the opening fixes `wsLen` and `fits` gives the bounds.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StateM5a.GlueRel

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.E2E.SB NearSpecV3.E2E.M8 NearSpecV3.Wasm NearSpecV3.E2E.Glue
open StateM5a.StateView
open StateM5a.StHalfC (updE updE1)

abbrev Bytes := NearSpec.Bytes

/-- **Lane B's state half for lane E's STATE instance, relational.** -/
def StHalfRelS (HoldsS : KV → Option Bytes → Option Bytes → Prop)
    (root : Intake → PTrie → (Bytes → Option (Option Bytes)) → Bytes) (Bad : Prop) : Prop :=
  ∀ q r r', HoldsS q r r' → Bad ∨ ∀ I t f, r = some (root I t f) → r' = some (root I t (updK q f))

/-- **STATE is relatively, canonically sound** from lane F's engine half and lane B's relational
state half (lane E's `state_reqs` supplies the glue; no `ApplyFaithfulS`). -/
theorem state_sound_relC_rel (sf : Intake → TTN.Store) (V : ViewImpl) {A : Airs8} {HoldsE HoldsS joint}
    (root : Intake → PTrie → (Bytes → Option (Option Bytes)) → Bytes)
    (apply : KV → Bytes → Bytes) (Bad : Prop)
    (hE : EngHalfRCOn sf V (stateSem (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS)
      (joint := joint) root apply) StatePre Bad)
    (hS : StHalfRelS HoldsS root Bad) : TmplSoundRel8C sf V A Bad .state := by
  intro ctx b b' tr hh x hc hx
  obtain ⟨q, r, r', h1, h2⟩ := joint ctx b b' tr hh
  rcases hE ctx b b' q r r' h1 x hc hx with hb | ⟨x', hc', hm, hl, hp, hr, hq, hout⟩
  · exact .inl hb
  rcases hS q r r' h2 with hb | hS'
  · exact .inl hb
  refine .inr ⟨x', hc', hout ?_, hm, hl⟩
  obtain ⟨o, o', ho, ho', ht, hk⟩ := state_reqs hm hp
  cases hm with
  | @run I c c' _ =>
  have hq' : q = netQ o o' := by
    rw [hq]; show (match ovE _, ovE _ with | some o, some o' => netQ o o' | _, _ => []) = _
    rw [ho, ho']
  have hr' : r = some (root I o.trie (kv o)) := by
    rw [← hr]; show wS root _ = _; simp only [wS, intakeOf, ho]
  have e := hS' I o.trie (kv o) hr'
  show wS root _ = r'
  simp only [wS, intakeOf, ho', ht, e, hq', show kv o' = updK (netQ o o') (kv o) from funext hk]

/-- Lane B's entry from a trie and a committed lookup (lane E's `GlueB.entryOf`, restated: that
file is not a lake module). -/
def entryOfT (t : PTrie) (f : Bytes → Option (Option Bytes)) (k : Bytes) : Entry :=
  match f k with
  | some x => (k, (t.find (nibbles k)).getD none, x, true)
  | none => (k, (t.find (nibbles k)).getD none, (t.find (nibbles k)).getD none, false)

/-- **The entries of the updated lookup are `updE` of the entries.** -/
theorem entries_updK (t : PTrie) (f : Bytes → Option (Option Bytes)) (q : KV) (K : List Bytes) :
    K.map (entryOfT t (updK q f)) = updE q (K.map (entryOfT t f)) := by
  simp only [updE, List.map_map]
  apply List.map_congr_left
  intro k _
  have hk : (entryOfT t f k).1 = k := by unfold entryOfT; split <;> rfl
  have h2 : (entryOfT t f k).2.1 = (t.find (nibbles k)).getD none := by unfold entryOfT; split <;> rfl
  simp only [Function.comp]
  unfold updE1
  rw [hk]
  cases hq : kvFind k q with
  | some x =>
    simp only [hq]
    rw [h2]
    simp only [entryOfT, updK, hq]
  | none =>
    simp only [entryOfT, updK, hq]

#print axioms state_sound_relC_rel
#print axioms entries_updK

end StateM5a.GlueRel
