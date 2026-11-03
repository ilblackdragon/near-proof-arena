import NearSpecV3.D2.State
import NearSpec.TrieUpsertProofs

/-!
# StateM5a.Steps — each `BR` / `SN` row operation is one step of the spec's trie recursion

The walk rows implement `PTrie.findRef` (INTAKE), `PTrie.upsert` and `PTrie.del` (FINAL, through
`applyChange`) one node at a time.  Each theorem below says that the spec function, applied at a
node of the shape the row holds, equals the row's rule in terms of the child's result: the selected
slot `Kids.at cs n`, the rewritten children `Kids.put cs n c'` and the memory-usage arithmetic the
row's limb chain computes.  So a chain of rows whose results are linked by `UP` computes exactly the
spec's result.

| row op | spec step |
|---|---|
| `BR.oFD` / `oFA` | `br_findRef` |
| `BR.oUD` / `oUN` | `br_upsert_descend` / `br_upsert_new` |
| `BR.oDH` / `oDL` / `oDN` | `br_del_keep` (with `squashBranch_keep`) |
| `BR.oD1` | `br_del_one` (`squashBranch` → `extendChild [i] (leaf …)`) |
| `SN.oLF` / `oLR` / `oLD` | `leaf_findRef` / `leaf_upsert` / `leaf_del` |
| `SN.oEF` / `oEU` / `oED` | `ext_findRef` / `ext_upsert` / `ext_del_leaf` |
| `SN.oLM` | `newLeaf`, `leafMem` (definitional) |

Axioms: `propext`, `Classical.choice`, `Quot.sound` only (checked in `StateM5a.Audit`).
-/

namespace StateM5a.Steps

open NearSpec NearSpecV3.D2

/-- Number of child slots. -/
def kidsLen : Kids → Nat
  | .nil => 0
  | .none r => kidsLen r + 1
  | .some _ r => kidsLen r + 1

/-! ## Kids: slot access -/

theorem kids_findRef_at : ∀ (cs : Kids) (n : Nat) (rest : List Nat),
    Kids.findRef cs n rest = (match Kids.at cs n with
      | some c => c.findRef rest
      | none => some none)
  | .nil, n, rest => by cases n <;> rfl
  | .none r, 0, rest => rfl
  | .some c r, 0, rest => rfl
  | .none r, n + 1, rest => by
    simp only [Kids.findRef, Kids.at]; exact kids_findRef_at r n rest
  | .some c r, n + 1, rest => by
    simp only [Kids.findRef, Kids.at]; exact kids_findRef_at r n rest

theorem kids_upsert_at : ∀ (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes),
    Kids.upsert cs n key v = (match Kids.at cs n with
      | some c => (match c.mem?, c.upsert key v with
          | some cm, some c' => some (Kids.put cs n (some c'), cm, c'.memD)
          | _, _ => none)
      | none => if n < kidsLen cs then
          some (Kids.put cs n (some (newLeaf key v)), 0, leafMem key v.length) else none)
  | .nil, n, key, v => by cases n <;> rfl
  | .none r, 0, key, v => by simp [Kids.upsert, Kids.at, Kids.put, kidsLen]
  | .some c r, 0, key, v => by
    simp only [Kids.upsert, Kids.at, Kids.put]
    cases c.mem? <;> cases c.upsert key v <;> rfl
  | .none r, n + 1, key, v => by
    simp only [Kids.upsert, Kids.at, Kids.put, kidsLen]
    rw [kids_upsert_at r n key v]
    cases h : Kids.at r n with
    | some c =>
      simp only
      cases c.mem? <;> cases c.upsert key v <;> rfl
    | none =>
      simp only
      by_cases hn : n < kidsLen r
      · simp [hn]
      · simp [hn]
  | .some x r, n + 1, key, v => by
    simp only [Kids.upsert, Kids.at, Kids.put, kidsLen]
    rw [kids_upsert_at r n key v]
    cases h : Kids.at r n with
    | some c =>
      simp only
      cases c.mem? <;> cases c.upsert key v <;> rfl
    | none =>
      simp only
      by_cases hn : n < kidsLen r
      · simp [hn]
      · simp [hn]

/-- The deleted-child memory usage `Kids.delAt` reports. -/
def delMem : Option PTrie → Nat
  | some c => c.memD
  | none => 0

theorem kids_delAt_at : ∀ (cs : Kids) (n : Nat) (key : List Nat),
    Kids.delAt cs n key = (match Kids.at cs n with
      | none => some none
      | some c => (match c.mem?, c.del key with
          | some cm, some (true, c') => some (some (Kids.put cs n c', cm, delMem c'))
          | some _, some (false, _) => some none
          | _, _ => none))
  | .nil, n, key => by cases n <;> rfl
  | .none r, 0, key => rfl
  | .some c r, 0, key => by
    simp only [Kids.delAt, Kids.at]
    cases c.mem? with
    | none => rfl
    | some cm =>
      cases hd : c.del key with
      | none => rfl
      | some p =>
        obtain ⟨b, c'⟩ := p
        cases b <;> cases c' <;> rfl
  | .none r, n + 1, key => by
    simp only [Kids.delAt, Kids.at, Kids.put]
    rw [kids_delAt_at r n key]
    cases Kids.at r n with
    | none => rfl
    | some c =>
      simp only
      cases c.mem? with
      | none => rfl
      | some cm =>
        cases c.del key with
        | none => rfl
        | some p =>
          obtain ⟨b, c'⟩ := p
          cases b <;> rfl
  | .some x r, n + 1, key => by
    simp only [Kids.delAt, Kids.at, Kids.put]
    rw [kids_delAt_at r n key]
    cases Kids.at r n with
    | none => rfl
    | some c =>
      simp only
      cases c.mem? with
      | none => rfl
      | some cm =>
        cases c.del key with
        | none => rfl
        | some p =>
          obtain ⟨b, c'⟩ := p
          cases b <;> rfl

/-! ## Branch rows -/

/-- `BR.oFD` / `BR.oFA`: the find descends into slot `n`, or answers "absent" at an empty slot. -/
theorem br_findRef (v : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) :
    PTrie.findRef (.branch v cs m) (n :: rest) = (match Kids.at cs n with
      | some c => c.findRef rest
      | none => some none) := by
  simp only [PTrie.findRef]; exact kids_findRef_at cs n rest

/-- `BR.oUD`: upsert through child `c` (old usage `cm`, result `c'`): the branch keeps its value
and slots, slot `n` becomes `c'`, usage `m + c'.memD − cm` (the row's limb chain). -/
theorem br_upsert_descend (bv : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (val : Bytes)
    (c c' : PTrie) (cm : Nat) (hc : Kids.at cs n = some c) (hm : c.mem? = some cm)
    (hu : c.upsert rest val = some c') :
    PTrie.upsert (.branch bv cs m) (n :: rest) val =
      some (.branch bv (Kids.put cs n (some c')) (m + c'.memD - cm)) := by
  simp only [PTrie.upsert, kids_upsert_at, hc, hm, hu, Option.map_some]

/-- `BR.oUN`: upsert into the empty slot `n` (of a 16-slot branch): a new leaf `rest ↦ val`
(materialized by `SN.oLM`), usage `m + leafMem rest |val|`. -/
theorem br_upsert_new (bv : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (val : Bytes)
    (hc : Kids.at cs n = none) (hn : n < kidsLen cs) :
    PTrie.upsert (.branch bv cs m) (n :: rest) val =
      some (.branch bv (Kids.put cs n (some (newLeaf rest val))) (m + leafMem rest val.length - 0)) := by
  simp only [PTrie.upsert, kids_upsert_at, hc, hn, ite_true, Option.map_some]

/-- `squashBranch` keeps the branch when one or more slots remain and, without a value, more
than one: the `BR` keep condition (`inv1·nk' = 1`, `inv2·(nk' − 1) = 1 − hasv`). -/
theorem squashBranch_keep (v : Option Slot) (cs : Kids) (m : Nat)
    (h0 : Kids.present cs 0 ≠ []) (h1 : v = none → (Kids.present cs 0).length ≠ 1) :
    squashBranch v cs m = some (some (.branch v cs m)) := by
  unfold squashBranch
  match hp : Kids.present cs 0, v with
  | [], _ => exact absurd hp h0
  | [_], none => exact absurd (by rw [hp]; rfl) (h1 rfl)
  | [_], some _ => rfl
  | _ :: _ :: _, none => rfl
  | _ :: _ :: _, some _ => rfl

/-- `BR.oDH` / `oDL` / `oDN`: delete through child `c`; its result `c'` (a hashed node, a leaf
materialized from its descriptor, or nothing) replaces slot `n`, usage `m − cm + delMem c'`, and
the branch is kept. -/
theorem br_del_keep (v : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat)
    (c : PTrie) (c' : Option PTrie) (cm : Nat) (hc : Kids.at cs n = some c) (hm : c.mem? = some cm)
    (hd : c.del rest = some (true, c'))
    (h0 : Kids.present (Kids.put cs n c') 0 ≠ [])
    (h1 : v = none → (Kids.present (Kids.put cs n c') 0).length ≠ 1) :
    PTrie.del (.branch v cs m) (n :: rest) =
      some (true, some (.branch v (Kids.put cs n c') (m - cm + delMem c'))) := by
  simp only [PTrie.del, kids_delAt_at, hc, hm, hd]
  rw [squashBranch_keep v _ _ h0 h1]
  rfl

/-- `BR.oD1`: the deleted child vanished and the one remaining slot `i` holds a leaf `k2 ↦ s`
(read by `SN.oLS`): the result is the leaf `[i] ++ k2 ↦ s` (a leaf descriptor upward). -/
theorem br_del_one (cs : Kids) (m n i : Nat) (rest k2 : List Nat) (c : PTrie) (cm : Nat) (s : Slot)
    (m2 : Nat) (hc : Kids.at cs n = some c) (hm : c.mem? = some cm)
    (hd : c.del rest = some (true, none))
    (hp : Kids.present (Kids.put cs n none) 0 = [(i, .leaf k2 s m2)]) :
    PTrie.del (.branch none cs m) (n :: rest) =
      some (true, some (.leaf ([i] ++ k2) s (leafMem ([i] ++ k2) s.len))) := by
  simp only [PTrie.del, kids_delAt_at, hc, hm, hd]
  unfold squashBranch
  rw [hp]
  rfl

/-! ## Leaf rows -/

/-- `SN.oLF`: the find ends at a leaf with the walk's remaining key. -/
theorem leaf_findRef (k : List Nat) (s : Slot) (m : Nat) :
    PTrie.findRef (.leaf k s m) k = some (some s) := by simp [PTrie.findRef]

/-- `SN.oLR`: upsert replaces the leaf by `newLeaf k val` (usage `leafMem k |val|`). -/
theorem leaf_upsert (k : List Nat) (s : Slot) (m : Nat) (val : Bytes) :
    PTrie.upsert (.leaf k s m) k val = some (newLeaf k val) := by simp [PTrie.upsert]

/-- `SN.oLD`: delete removes the leaf (result kind `NONE`). -/
theorem leaf_del (k : List Nat) (s : Slot) (m : Nat) :
    PTrie.del (.leaf k s m) k = some (true, none) := by simp [PTrie.del]

/-- `newLeaf`'s usage is the row's `100 + 2·|hp| + |v|`. -/
theorem leafMem_eq (k : List Nat) (vlen : Nat) :
    leafMem k vlen = 100 + 2 * (hexPrefix k true).length + vlen := by
  unfold leafMem; omega

/-! ## Extension rows -/

/-- `SN.oEF`: the find descends below an extension whose key is the next part of the walk key. -/
theorem ext_findRef (k : List Nat) (c : PTrie) (m : Nat) (rest : List Nat) :
    PTrie.findRef (.ext k c m) (k ++ rest) = c.findRef rest := by
  simp [PTrie.findRef, isPrefix_append]

/-- `SN.oEU`: upsert below an extension: usage `m + c'.memD − cm`. -/
theorem ext_upsert (k : List Nat) (c c' : PTrie) (m cm : Nat) (rest : List Nat) (val : Bytes)
    (hm : c.mem? = some cm) (hu : c.upsert rest val = some c') :
    PTrie.upsert (.ext k c m) (k ++ rest) val = some (.ext k c' (m + c'.memD - cm)) := by
  simp [PTrie.upsert, isPrefix_append, hm, hu]

/-- `SN.oED`: delete below an extension whose child result is a leaf `k2 ↦ s`: the extension and
the leaf merge (`extendChild`) into the leaf `k ++ k2 ↦ s` (the forwarded leaf descriptor). -/
theorem ext_del_leaf (k : List Nat) (c : PTrie) (m cm : Nat) (rest k2 : List Nat) (s : Slot) (m2 : Nat)
    (hm : c.mem? = some cm) (hd : c.del rest = some (true, some (.leaf k2 s m2))) :
    PTrie.del (.ext k c m) (k ++ rest) =
      some (true, some (.leaf (k ++ k2) s (leafMem (k ++ k2) s.len))) := by
  simp [PTrie.del, isPrefix_append, hm, hd, extendChild]

/-! ## `applyChange` at the root (FINAL) -/

/-- A present final value is an upsert, an absent one a delete; the walk's root result is the new
trie and `rootHash` its digest. -/
theorem applyChange_upsert (t : PTrie) (k x : Bytes) (t' : PTrie)
    (h : t.upsert (nibbles k) x = some t') :
    applyChange (some t) k (some x) = some (some t') := by
  simp [applyChange, h]

theorem applyChange_del (t : PTrie) (k : Bytes) (t' : PTrie)
    (h : t.del (nibbles k) = some (true, some t')) :
    applyChange (some t) k none = some (some t') := by
  simp [applyChange, h]

end StateM5a.Steps
