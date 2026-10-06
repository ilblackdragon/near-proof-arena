import ZkFormal.NearV3.Extract.Ups.UpsRoot
import ZkFormal.NearV3.Extract.Ups.SpbSplit

/-!
# ZkFormal.NearV3.Extract.Ups.UpsUpsert — `PTrie.upsert` one node at a time (M7e, step 3, spec side)

Each part's target node is what `PTrie.upsert` builds at its node, given the key facts the walk supplies:

* **`kids_upsert_some`** / **`kids_upsert_none`**: upserting into an occupied / empty slot replaces / inserts
  that child (`setKid`), with the old and new child usage;
* **`upsert_rdb`**, **`upsert_rde`**, **`upsert_pt`**: a descend through a branch slot / an extension and a
  pass-through give `qRDB`, `qRDE`, `qPT` from the child's upsert;
* terminal nodes: **`upsert_rlp`** (present leaf), **`upsert_rbr`** / **`upsert_rbv`** (branch value replaced /
  set), **`upsert_rbi`** (empty slot), **`upsert_leafSplit`** / **`upsert_extSplit`** (a leaf / an extension that
  is not on the key: `splitLeaf` / `splitExt`, then `SpbSplit`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open NearSpec UpsSpec

theorem kids_upsert_some : ∀ (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes) (c c' : PTrie) (cm : Nat),
    kidAt cs n = some c → c.mem? = some cm → c.upsert key v = some c' →
    Kids.upsert cs n key v = some (setKid cs n c', cm, c'.memD)
  | .nil, _, _, _, _, _, _, h, _, _ => by simp [kidAt] at h
  | .none r, 0, _, _, _, _, _, h, _, _ => by simp [kidAt] at h
  | .some d r, 0, key, v, c, c', cm, h, hm, hu => by
    simp only [kidAt, Option.some.injEq] at h
    subst h
    simp [Kids.upsert, hm, hu, setKid]
  | .none r, n + 1, key, v, c, c', cm, h, hm, hu => by
    simp only [kidAt] at h
    simp [Kids.upsert, kids_upsert_some r n key v c c' cm h hm hu, setKid]
  | .some d r, n + 1, key, v, c, c', cm, h, hm, hu => by
    simp only [kidAt] at h
    simp [Kids.upsert, kids_upsert_some r n key v c c' cm h hm hu, setKid]

theorem kids_upsert_none : ∀ (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes),
    n < kidsLen cs → kidAt cs n = none →
    Kids.upsert cs n key v = some (setKid cs n (newLeaf key v), 0, leafMem key v.length)
  | .nil, _, _, _, hl, _ => by simp [kidsLen] at hl
  | .none r, 0, key, v, _, _ => by simp [Kids.upsert, setKid]
  | .some d r, 0, _, _, _, h => by simp [kidAt] at h
  | .none r, n + 1, key, v, hl, h => by
    simp only [kidAt] at h; simp only [kidsLen] at hl
    simp [Kids.upsert, kids_upsert_none r n key v (by omega) h, setKid]
  | .some d r, n + 1, key, v, hl, h => by
    simp only [kidAt] at h; simp only [kidsLen] at hl
    simp [Kids.upsert, kids_upsert_none r n key v (by omega) h, setKid]

/-- **A descend through a branch slot.** -/
theorem upsert_rdb (bv : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (v : Bytes) (c c' : PTrie)
    (hc : kidAt cs n = some c) (hcm : c.mem? = some c.memD) (hu : c.upsert rest v = some c') :
    (PTrie.branch bv cs m).upsert (n :: rest) v = some (qRDB bv cs m n c' c.memD) := by
  simp [PTrie.upsert, kids_upsert_some cs n rest v c c' c.memD hc hcm hu, qRDB]

/-- **A descend through an extension** whose key is a prefix of the lookup key. -/
theorem upsert_rde (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) (c' : PTrie)
    (hk : key.take k.length = k) (hcm : c.mem? = some c.memD) (hu : c.upsert (key.drop k.length) v = some c') :
    (PTrie.ext k c m).upsert key v = some (qRDE k m c' c.memD) := by
  have hp : isPrefix k key = true := by
    rw [isPrefix_iff]; exact ⟨key.drop k.length, by conv => lhs; rw [← List.take_append_drop k.length key, hk]⟩
  simp [PTrie.upsert, hp, hcm, hu, qRDE]

/-- **A pass-through** (`.ext []`). -/
theorem upsert_pt (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) (c' : PTrie)
    (hcm : c.mem? = some c.memD) (hu : c.upsert key v = some c') :
    (PTrie.ext [] c m).upsert key v = some (qPT m c' c.memD) := by
  have := upsert_rde [] c m key v c' (by simp) hcm (by simpa using hu)
  simpa [qRDE, qPT] using this

/-- **A present leaf.** -/
theorem upsert_rlp (k : List Nat) (s : Slot) (m : Nat) (v : Bytes) :
    (PTrie.leaf k s m).upsert k v = some (qRLP k v) := by
  simp [PTrie.upsert, qRLP]

/-- **A branch value replaced.** -/
theorem upsert_rbr (s : Slot) (cs : Kids) (m : Nat) (v : Bytes) :
    (PTrie.branch (some s) cs m).upsert [] v = some (qRBR s cs m v) := by
  simp [PTrie.upsert, qRBR]

/-- **A branch value set.** -/
theorem upsert_rbv (cs : Kids) (m : Nat) (v : Bytes) :
    (PTrie.branch none cs m).upsert [] v = some (qRBV cs m v) := by
  simp [PTrie.upsert, qRBV]

/-- **An empty branch slot.** -/
theorem upsert_rbi (bv : Option Slot) (cs : Kids) (m si : Nat) (v : Bytes) (hsi : si < 2)
    (hl : yOf si < kidsLen cs) (hy : kidAt cs (yOf si) = none) :
    (PTrie.branch bv cs m).upsert (key.drop si) v = some (qRBI bv cs m si v) := by
  rw [key_drop si hsi]
  simp [PTrie.upsert, kids_upsert_none cs (yOf si) (ysOf si) v hl hy, qRBI, qNLF]

/-- **A leaf off the key.** -/
theorem upsert_leafSplit (k : List Nat) (s : Slot) (m : Nat) (key' : List Nat) (v : Bytes) (hne : k ≠ key') :
    (PTrie.leaf k s m).upsert key' v = some (splitLeaf k s key' v) := by
  simp [PTrie.upsert, hne]

/-- **An extension off the key.** -/
theorem upsert_extSplit (k : List Nat) (c : PTrie) (m : Nat) (key' : List Nat) (v : Bytes)
    (hne : key'.take k.length ≠ k) :
    (PTrie.ext k c m).upsert key' v = some (splitExt k c m key' v) := by
  have hp : isPrefix k key' = false := by
    cases h : isPrefix k key' with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨r, hr⟩ := (isPrefix_iff k key').1 h
      apply hne; rw [hr]; simp
  simp [PTrie.upsert, hp]

end ZkFormal.NearV3.UpsRows
