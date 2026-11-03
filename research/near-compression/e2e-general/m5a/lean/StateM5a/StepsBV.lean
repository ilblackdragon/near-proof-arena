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

The squash after a value delete that leaves one child (`extendChild [i] c`) is not in the menu
(a completeness gap, as the squash onto an extension or branch sibling).
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

end StateM5a.StepsBV
