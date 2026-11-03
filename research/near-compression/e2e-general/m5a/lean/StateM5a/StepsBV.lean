import StateM5a.Steps

/-!
# StateM5a.StepsBV — the branch-value rows (M5a-2 completeness)

A walk key that ends at a branch (a key that is a prefix of another key, e.g. a contract's storage
key `k` next to `k ‖ suffix`) reads, writes or deletes the branch's own value:

| row op | spec step |
|---|---|
| `BR.oFV` | `br_findValue` (`StepsT2`) |
| `BR.oUV` | `br_upsert_value`: the value is replaced, the children kept, memory `m + valueMem |x| − valueMem |old|` |
| `BR.oDV` | `br_del_value_keep`: the value is removed and the branch kept (≥ 2 children: `squashBranch`'s last case) |
| `BR.oDZ` | `br_del_value_absent`: no value, nothing deleted (`SAME`) |

The squash after a value delete that leaves one child (`extendChild [i] c`) is not in the row
menu (a completeness gap, as the squash onto an extension or branch sibling); its spec step is
stated here for a future row op (`br_del_value_one` and its three child shapes
`br_del_value_one_leaf` / `_ext` / `_branch`, and `br_del_value_none` for a value-only branch).

Memory (`Trie.Br.memNew`, `nm = om = 0` on `oUV` / `oDV`): `nmem = mem + oUV·(nvl + 50) −
(oUV·hasv + oDV)·(vl + 50)` on 4 limbs of 16 bits with no final carry, i.e. exactly
`m + valueMem |x| − valueMem |old|` (`oUV`) and `m − valueMem |old|` (`oDV`), the spec's
truncated subtractions whenever the row exists.
-/

namespace StateM5a.StepsBV

open NearSpec NearSpecV3.D2

theorem br_upsert_value (bv : Option Slot) (cs : Kids) (m : Nat) (x : Bytes) :
    (PTrie.branch bv cs m).upsert [] x =
      some (.branch (some (.val x)) cs
        (m + valueMem x.length - (match bv with | some s => valueMem s.len | none => 0))) := by
  cases bv <;> rfl

theorem br_del_value_keep (s : Slot) (cs : Kids) (m : Nat)
    (h : 2 ≤ (Kids.present cs 0).length) :
    (PTrie.branch (some s) cs m).del [] =
      some (true, some (.branch none cs (m - valueMem s.len))) := by
  simp only [PTrie.del, squashBranch]
  match hp : Kids.present cs 0, h with
  | _ :: _ :: _, _ => simp

theorem br_del_value_absent (cs : Kids) (m : Nat) :
    (PTrie.branch none cs m).del [] = some (false, some (.branch none cs m)) := by
  simp [PTrie.del]

/-! ## The squash after a value delete (spec steps; no row op yet) -/

/-- A value delete leaving exactly one child squashes it into its parent position:
`extendChild [i] c` (`squashBranch`'s one-child case, the value being gone). -/
theorem br_del_value_one (s : Slot) (cs : Kids) (m i : Nat) (c : PTrie)
    (hp : Kids.present cs 0 = [(i, c)]) :
    (PTrie.branch (some s) cs m).del [] = (extendChild [i] c).map fun r => (true, r) := by
  simp only [PTrie.del, squashBranch, hp]

/-- … onto a leaf child: one leaf with key `i :: k2` and its own canonical memory. -/
theorem br_del_value_one_leaf (s : Slot) (cs : Kids) (m i : Nat) (k2 : List Nat) (s2 : Slot)
    (m2 : Nat) (hp : Kids.present cs 0 = [(i, .leaf k2 s2 m2)]) :
    (PTrie.branch (some s) cs m).del [] =
      some (true, some (.leaf ([i] ++ k2) s2 (leafMem ([i] ++ k2) s2.len))) := by
  rw [br_del_value_one s cs m i _ hp]; rfl

/-- … onto an extension child: one extension with key `i :: k2` (memory: the new key's own cost
plus the child's, `m2 − extOwnMem k2`). -/
theorem br_del_value_one_ext (s : Slot) (cs : Kids) (m i : Nat) (k2 : List Nat) (c2 : PTrie)
    (m2 : Nat) (hp : Kids.present cs 0 = [(i, .ext k2 c2 m2)]) :
    (PTrie.branch (some s) cs m).del [] =
      some (true, some (.ext ([i] ++ k2) c2 (extOwnMem ([i] ++ k2) + (m2 - extOwnMem k2)))) := by
  rw [br_del_value_one s cs m i _ hp]; rfl

/-- … onto a branch child: a new one-nibble extension `[i]` above it. -/
theorem br_del_value_one_branch (s : Slot) (cs : Kids) (m i : Nat) (v2 : Option Slot) (cs2 : Kids)
    (m2 : Nat) (hp : Kids.present cs 0 = [(i, .branch v2 cs2 m2)]) :
    (PTrie.branch (some s) cs m).del [] =
      some (true, some (.ext [i] (.branch v2 cs2 m2) (extOwnMem [i] + m2))) := by
  rw [br_del_value_one s cs m i _ hp]; rfl

/-- … an unrevealed remaining child: the spec fails (`MissingTrieValue`). -/
theorem br_del_value_one_hash (s : Slot) (cs : Kids) (m i : Nat) (h : Bytes)
    (hp : Kids.present cs 0 = [(i, .hash h)]) : (PTrie.branch (some s) cs m).del [] = none := by
  rw [br_del_value_one s cs m i _ hp]; rfl

/-- A value-only branch (no children) deleted: the empty node. -/
theorem br_del_value_none (s : Slot) (cs : Kids) (m : Nat) (hp : Kids.present cs 0 = []) :
    (PTrie.branch (some s) cs m).del [] = some (true, none) := by
  simp only [PTrie.del, squashBranch, hp, Option.map_some]

end StateM5a.StepsBV
