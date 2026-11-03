import StateM5a.Steps

/-!
# StateM5a.StepsT2 — the rows added for T2, each one step of the spec's trie recursion

| row op | spec step |
|---|---|
| `BR.oFV` | `br_findValue`: a find ending at a branch answers its value |
| `BR.oDA` / `oDS` | `br_del_absent` / `br_del_same`: the branch is unchanged (`deleted = false`) |
| `SN.oLA` / `oLZ` | `leaf_findRef_absent` / `leaf_del_absent` (from `ne_of_mismatch`) |
| `SN.oEA` / `oEZ` | `ext_findRef_absent` / `ext_del_absent` (from `not_isPrefix_of_mismatch`) |
| `SN.oES` | `ext_del_same` |
| `SN.oEB` | `ext_del_branch` (`extendChild k (branch …)`) |
| `SN.oLX` + `BR.oSL` + `SN.oEP` | `leaf_split` (`splitLeaf`, two children) and `wrapExt_cons` |
| `SN.oEX` + `SN.oEM` + `BR.oSL` + `SN.oEP` | `ext_split` (`splitExt`, two children) |
| `BR.oSL` | `kids2_at`: the new branch's slots `x`, `y` (`Kids.at`) |

The mismatch witness of an absent / split row is one position `jm` where the row's key and the
walk key agree before `jm` and differ at `jm` as optional nibbles (`k[jm]? ≠ key[jm]?`): another
nibble (`mN`), the walk key ends (`mK`), or the leaf key ends (`mL`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only (checked in `StateM5a.Audit`).
-/

namespace StateM5a.Steps

open NearSpec NearSpecV3.D2

/-! ## The mismatch witness -/

/-- Keys that agree before `jm` and differ at `jm` (as optional nibbles) are different. -/
theorem ne_of_mismatch (k key : List Nat) (jm : Nat) (h : k[jm]? ≠ key[jm]?) : k ≠ key := by
  rintro rfl; exact h rfl

theorem take_eq_of_prefix {p l : List Nat} (h : isPrefix p l = true) : l.take p.length = p := by
  obtain ⟨r, rfl⟩ := (isPrefix_iff p l).1 h
  simp

/-- An extension key `k` is not a prefix of the walk key when they agree before `jm < |k|` and
differ at `jm`. -/
theorem not_isPrefix_of_mismatch (k key : List Nat) (jm : Nat) (hj : jm < k.length)
    (h : k[jm]? ≠ key[jm]?) : isPrefix k key = false := by
  cases hp : isPrefix k key with
  | false => rfl
  | true =>
    obtain ⟨r, rfl⟩ := (isPrefix_iff k key).1 hp
    exfalso; apply h
    rw [List.getElem?_append_left hj]

/-! ## Branch rows -/

/-- `BR.oFV`: a find whose key ends at a branch answers the branch value. -/
theorem br_findValue (v : Option Slot) (cs : Kids) (m : Nat) :
    PTrie.findRef (.branch v cs m) [] = some v := rfl

/-- `BR.oDA`: a delete reaching an empty slot leaves the branch unchanged. -/
theorem br_del_absent (v : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat)
    (hc : Kids.at cs n = none) :
    PTrie.del (.branch v cs m) (n :: rest) = some (false, some (.branch v cs m)) := by
  simp only [PTrie.del, kids_delAt_at, hc]

/-- `BR.oDS`: the child is unchanged (`deleted = false`), so is the branch. -/
theorem br_del_same (v : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (c : PTrie)
    (cm : Nat) (c'' : Option PTrie) (hc : Kids.at cs n = some c) (hm : c.mem? = some cm)
    (hd : c.del rest = some (false, c'')) :
    PTrie.del (.branch v cs m) (n :: rest) = some (false, some (.branch v cs m)) := by
  simp only [PTrie.del, kids_delAt_at, hc, hm, hd]

/-! ## Leaf rows -/

/-- `SN.oLA`: a find at a leaf with another key answers "absent". -/
theorem leaf_findRef_absent (k key : List Nat) (s : Slot) (m : Nat) (h : k ≠ key) :
    PTrie.findRef (.leaf k s m) key = some none := by
  simp [PTrie.findRef, h]

/-- `SN.oLZ`: a delete at a leaf with another key deletes nothing. -/
theorem leaf_del_absent (k key : List Nat) (s : Slot) (m : Nat) (h : k ≠ key) :
    PTrie.del (.leaf k s m) key = some (false, some (.leaf k s m)) := by
  simp [PTrie.del, h]

/-! ## Extension rows -/

/-- `SN.oEA`: a find whose key does not continue with the extension's key answers "absent". -/
theorem ext_findRef_absent (k key : List Nat) (c : PTrie) (m : Nat) (h : isPrefix k key = false) :
    PTrie.findRef (.ext k c m) key = some none := by
  simp [PTrie.findRef, h]

/-- `SN.oEZ`: likewise for a delete. -/
theorem ext_del_absent (k key : List Nat) (c : PTrie) (m : Nat) (h : isPrefix k key = false) :
    PTrie.del (.ext k c m) key = some (false, some (.ext k c m)) := by
  simp [PTrie.del, h]

/-- `SN.oES`: the child is unchanged, so is the extension. -/
theorem ext_del_same (k : List Nat) (c : PTrie) (m cm : Nat) (rest : List Nat) (c'' : Option PTrie)
    (hm : c.mem? = some cm) (hd : c.del rest = some (false, c'')) :
    PTrie.del (.ext k c m) (k ++ rest) = some (false, some (.ext k c m)) := by
  simp [PTrie.del, isPrefix_append, hm, hd]

/-- `SN.oEB`: the child's result is a kept branch (usage `m'`): `extendChild k` makes the new
extension `k ↦ branch` with usage `extOwnMem k + m'` (the row's fresh memory chain). -/
theorem ext_del_branch (k : List Nat) (c : PTrie) (m cm : Nat) (rest : List Nat) (bv : Option Slot)
    (cs : Kids) (m' : Nat) (hm : c.mem? = some cm) (hd : c.del rest = some (true, some (.branch bv cs m'))) :
    PTrie.del (.ext k c m) (k ++ rest) =
      some (true, some (.ext k (.branch bv cs m') (extOwnMem k + m'))) := by
  simp [PTrie.del, isPrefix_append, hm, hd, extendChild]

/-! ## Splits -/

theorem commonPrefix_split (p xs ys : List Nat) (x y : Nat) (hxy : x ≠ y) :
    commonPrefix (p ++ x :: xs) (p ++ y :: ys) = p := by
  induction p with
  | nil => simp [commonPrefix, hxy]
  | cons a p ih => simp [commonPrefix, ih]

/-- `SN.oEP`: the extension over a non-empty common prefix (`wrapExt`). -/
theorem wrapExt_cons (a : Nat) (p : List Nat) (b : PTrie) :
    wrapExt (a :: p) b = .ext (a :: p) b (extOwnMem (a :: p) + b.memD) := rfl

/-- `SN.oLX` (+ `BR.oSL`, two `SN.oLM`, `SN.oEP` when `p ≠ []`): an upsert at a leaf whose key
`p ++ x :: xs` differs from the walk key `p ++ y :: ys` at `x ≠ y` builds the branch with the
re-keyed old leaf at `x` and the new leaf at `y`, under `wrapExt p`. -/
theorem leaf_split (p xs ys : List Nat) (x y : Nat) (hxy : x ≠ y) (s : Slot) (m : Nat) (v : Bytes) :
    PTrie.upsert (.leaf (p ++ x :: xs) s m) (p ++ y :: ys) v =
      some (wrapExt p (.branch none (kids2 x (.leaf xs s (leafMem xs s.len)) y (newLeaf ys v))
        (50 + leafMem xs s.len + leafMem ys v.length))) := by
  have hne : p ++ x :: xs ≠ p ++ y :: ys := by
    intro h; exact hxy (List.cons.inj (List.append_cancel_left h)).1
  simp only [PTrie.upsert, hne, ↓reduceIte, splitLeaf, commonPrefix_split p xs ys x y hxy,
    List.drop_left']

/-- `SN.oEX` (+ `SN.oEM` when `xs ≠ []`, `BR.oSL`, `SN.oLM`, `SN.oEP` when `p ≠ []`): an upsert at
an extension `p ++ x :: xs` (child `c`, usage `m`) that the walk key `p ++ y :: ys` leaves at
`x ≠ y`.  The old-side child is `c` itself (usage `cm = m − extOwnMem k`) or the re-keyed
extension `xs ↦ c` (usage `extOwnMem xs + cm`). -/
theorem ext_split (p xs ys : List Nat) (x y : Nat) (hxy : x ≠ y) (c : PTrie) (m : Nat) (v : Bytes) :
    PTrie.upsert (.ext (p ++ x :: xs) c m) (p ++ y :: ys) v =
      some (let cm := m - extOwnMem (p ++ x :: xs)
        let sub : PTrie := match xs with
          | [] => c
          | _ :: _ => .ext xs c (extOwnMem xs + cm)
        let subMem := match xs with
          | [] => cm
          | _ :: _ => extOwnMem xs + cm
        wrapExt p (.branch none (kids2 x sub y (newLeaf ys v)) (50 + subMem + leafMem ys v.length))) := by
  have hnp : isPrefix (p ++ x :: xs) (p ++ y :: ys) = false := by
    rw [isPrefix_append_append, isPrefix_cons_cons]
    simp [hxy]
  simp only [PTrie.upsert, hnp, Bool.false_eq_true, ↓reduceIte, splitExt,
    commonPrefix_split p xs ys x y hxy, List.drop_left']
  rfl

/-! ## The split branch's slots -/

theorem kidsFrom_at (f : Nat → Option PTrie) : ∀ (n i j : Nat), j < n →
    Kids.at (kidsFrom n i f) j = f (i + j)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, 0, _ => by
    simp only [kidsFrom]; cases f i <;> simp [Kids.at]
  | n + 1, i, j + 1, h => by
    have := kidsFrom_at f n (i + 1) j (by omega)
    simp only [kidsFrom]
    cases f i <;> simp only [Kids.at] <;> rw [this] <;> congr 1 <;> omega

/-- `BR.oSL`'s children: slot `x` holds the old-side child, slot `y` the new leaf, no others. -/
theorem kids2_at (x y : Nat) (c d : PTrie) (j : Nat) (hj : j < 16) :
    Kids.at (kids2 x c y d) j = if j = x then some c else if j = y then some d else none := by
  unfold kids2; rw [kidsFrom_at _ 16 0 j hj]; simp

end StateM5a.Steps
