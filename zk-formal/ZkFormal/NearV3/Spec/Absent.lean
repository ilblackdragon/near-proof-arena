import ZkFormal.NearV3.Spec.TrieOps
import NearSpecV3.RuntimeD0

/-!
# ZkFormal.NearV3.Spec.Absent — non-membership witnesses

`AbsentWitness t key` is the spec-level form of a `walk` ending in an *absent*
terminal (V3-D0-DESIGN §3.2.4): the lookup descends through revealed branches
and extensions and stops at

* `brSlot` — a branch whose child slot for the next nibble is empty (`ABS_BR`);
* `brVal` — the key ends at a branch with no value (`ABS_VAL`);
* `extNib` / `leafNib` — a key nibble differs from the extension / leaf key
  nibble at the same position (`ABS_KEY`, `nib ≠ sym`);
* `extLen` — the key ends inside the extension key (`ABS_KEY`, key ended);
* `leafLen` — the leaf key and the remaining key have different lengths
  (`ABS_KEY`, one key ended before the other).

* `absent_find` (soundness): `AbsentWitness t key → t.find key = some none`;
* `absent_of_find` (completeness): `t.find key = some none → AbsentWitness t key`;
* `upsert_absent` (insertion): along a witness, `upsert` always succeeds (every
  node on the path is revealed), the new key maps to the value and every other
  key is unchanged; `upsert_brSlot`, `upsert_brVal`, `upsert_leaf_ne`,
  `upsert_ext_np`, `upsert_branch_down`, `upsert_ext_down` give the local
  rewrite at each step (what the AIR's insertion mode must implement for
  `0x0f` = nibbles `[0, 15]`).
-/

namespace ZkFormal.NearV3

open NearSpec

/-- Child `n` of a branch (`none`: empty slot or out of range). -/
def Kids.slot : Kids → Nat → Option PTrie
  | .nil, _ => none
  | .none _, 0 => none
  | .some c _, 0 => some c
  | .none r, i + 1 => Kids.slot r i
  | .some _ r, i + 1 => Kids.slot r i

theorem Kids.find_slot : ∀ (cs : Kids) (n : Nat) (key : List Nat),
    Kids.find cs n key = match Kids.slot cs n with
      | none => some none
      | some c => c.find key
  | .nil, _, _ => by simp [Kids.find, Kids.slot]
  | .none _, 0, _ => by simp [Kids.find, Kids.slot]
  | .some _ _, 0, _ => by simp [Kids.find, Kids.slot]
  | .none r, i + 1, key => by simp only [Kids.find, Kids.slot]; exact Kids.find_slot r i key
  | .some _ r, i + 1, key => by simp only [Kids.find, Kids.slot]; exact Kids.find_slot r i key

/-- A proof that `key` is absent from the revealed part of `t`. -/
inductive AbsentWitness : PTrie → List Nat → Prop
  | brSlot {bv : Option Slot} {cs : Kids} {m n : Nat} {rest : List Nat} :
      Kids.slot cs n = none → AbsentWitness (.branch bv cs m) (n :: rest)
  | brVal {cs : Kids} {m : Nat} : AbsentWitness (.branch none cs m) []
  | brDown {bv : Option Slot} {cs : Kids} {m n : Nat} {rest : List Nat} {c : PTrie} :
      Kids.slot cs n = some c → AbsentWitness c rest → AbsentWitness (.branch bv cs m) (n :: rest)
  | extDown {k : List Nat} {c : PTrie} {m : Nat} {key : List Nat} :
      isPrefix k key = true → AbsentWitness c (key.drop k.length) → AbsentWitness (.ext k c m) key
  | extNib {k : List Nat} {c : PTrie} {m : Nat} {key : List Nat} {i a b : Nat} :
      k[i]? = some a → key[i]? = some b → a ≠ b → AbsentWitness (.ext k c m) key
  | extLen {k : List Nat} {c : PTrie} {m : Nat} {key : List Nat} :
      key.length < k.length → AbsentWitness (.ext k c m) key
  | leafNib {k : List Nat} {s : Slot} {m : Nat} {key : List Nat} {i a b : Nat} :
      k[i]? = some a → key[i]? = some b → a ≠ b → AbsentWitness (.leaf k s m) key
  | leafLen {k : List Nat} {s : Slot} {m : Nat} {key : List Nat} :
      k.length ≠ key.length → AbsentWitness (.leaf k s m) key

/-! ## List facts -/

theorem ne_of_nib {k key : List Nat} {i a b : Nat} (ha : k[i]? = some a) (hb : key[i]? = some b)
    (hab : a ≠ b) : k ≠ key := by
  intro e; subst e; rw [ha] at hb; exact hab (Option.some.inj hb)

theorem not_prefix_of_nib : ∀ {k key : List Nat} {i a b : Nat}, k[i]? = some a → key[i]? = some b →
    a ≠ b → isPrefix k key = false
  | [], _, _, _, _, ha, _, _ => by simp at ha
  | _ :: _, [], _, _, _, _, hb, _ => by simp at hb
  | x :: xs, y :: ys, 0, a, b, ha, hb, hab => by
    simp at ha hb; subst ha hb; simp [isPrefix, hab]
  | x :: xs, y :: ys, i + 1, a, b, ha, hb, hab => by
    simp at ha hb
    simp [isPrefix, not_prefix_of_nib ha hb hab]

theorem not_prefix_of_len : ∀ {k key : List Nat}, key.length < k.length → isPrefix k key = false
  | [], _, h => by simp at h
  | _ :: _, [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp at h; simp [isPrefix, not_prefix_of_len (k := xs) (key := ys) (by omega)]

theorem nib_or_len_of_ne : ∀ {k key : List Nat}, k ≠ key →
    (∃ (i a b : Nat), k[i]? = some a ∧ key[i]? = some b ∧ a ≠ b) ∨ k.length ≠ key.length
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => Or.inr (by simp)
  | _ :: _, [], _ => Or.inr (by simp)
  | x :: xs, y :: ys, h => by
    by_cases hxy : x = y
    · subst hxy
      have : xs ≠ ys := fun e => h (by rw [e])
      rcases nib_or_len_of_ne this with ⟨i, a, b, ha, hb, hab⟩ | hl
      · exact Or.inl ⟨i + 1, a, b, by simpa using ha, by simpa using hb, hab⟩
      · exact Or.inr (by simpa using hl)
    · exact Or.inl ⟨0, x, y, by simp, by simp, hxy⟩

theorem nib_or_len_of_not_prefix : ∀ {k key : List Nat}, isPrefix k key = false →
    (∃ (i a b : Nat), k[i]? = some a ∧ key[i]? = some b ∧ a ≠ b) ∨ key.length < k.length
  | [], _, h => by simp [isPrefix] at h
  | _ :: _, [], _ => Or.inr (by simp)
  | x :: xs, y :: ys, h => by
    by_cases hxy : x = y
    · subst hxy
      have : isPrefix xs ys = false := by simpa [isPrefix] using h
      rcases nib_or_len_of_not_prefix this with ⟨i, a, b, ha, hb, hab⟩ | hl
      · exact Or.inl ⟨i + 1, a, b, by simpa using ha, by simpa using hb, hab⟩
      · exact Or.inr (by simpa using hl)
    · exact Or.inl ⟨0, x, y, by simp, by simp, hxy⟩

/-! ## Soundness and completeness -/

/-- **Soundness**: a witness proves absence. -/
theorem absent_find {t : PTrie} {key : List Nat} (h : AbsentWitness t key) : t.find key = some none := by
  induction h with
  | brSlot hs => simp [PTrie.find, Kids.find_slot, hs]
  | brVal => simp [PTrie.find]
  | brDown hs _ ih => simp [PTrie.find, Kids.find_slot, hs, ih]
  | extDown hp _ ih => simp [PTrie.find, hp, ih]
  | extNib ha hb hab => simp [PTrie.find, not_prefix_of_nib ha hb hab]
  | extLen hl => simp [PTrie.find, not_prefix_of_len hl]
  | leafNib ha hb hab => simp [PTrie.find, ne_of_nib ha hb hab]
  | leafLen hl => simp [PTrie.find]; intro e; subst e; exact hl rfl

mutual
/-- **Completeness**: every proven absence has a witness. -/
theorem absent_of_find : ∀ (t : PTrie) (key : List Nat), t.find key = some none → AbsentWitness t key
  | .hash _, _, h => by simp [PTrie.find] at h
  | .leaf k s m, key, h => by
    simp only [PTrie.find] at h
    by_cases e : k = key
    · subst e; cases hs : s.get <;> simp [hs] at h
    · rcases nib_or_len_of_ne e with ⟨i, a, b, ha, hb, hab⟩ | hl
      · exact .leafNib ha hb hab
      · exact .leafLen hl
  | .ext k c m, key, h => by
    simp only [PTrie.find] at h
    by_cases hp : isPrefix k key = true
    · simp only [hp, ↓reduceIte] at h
      exact .extDown hp (absent_of_find c _ h)
    · have hp' : isPrefix k key = false := by simpa using hp
      rcases nib_or_len_of_not_prefix hp' with ⟨i, a, b, ha, hb, hab⟩ | hl
      · exact .extNib ha hb hab
      · exact .extLen hl
  | .branch bv cs m, [], h => by
    cases bv with
    | none => exact .brVal
    | some s => simp only [PTrie.find] at h; cases hs : s.get <;> simp [hs] at h
  | .branch bv cs m, n :: rest, h => by
    simp only [PTrie.find] at h
    rcases kids_absent cs n rest h with hs | ⟨c, hs, hc⟩
    · exact .brSlot hs
    · exact .brDown hs hc
theorem kids_absent : ∀ (cs : Kids) (n : Nat) (rest : List Nat), Kids.find cs n rest = some none →
    Kids.slot cs n = none ∨ ∃ c, Kids.slot cs n = some c ∧ AbsentWitness c rest
  | .nil, _, _, _ => Or.inl rfl
  | .none _, 0, _, _ => Or.inl rfl
  | .some c _, 0, rest, h => Or.inr ⟨c, rfl, absent_of_find c rest (by simpa [Kids.find] using h)⟩
  | .none r, i + 1, rest, h => kids_absent r i rest (by simpa [Kids.find] using h)
  | .some _ r, i + 1, rest, h => kids_absent r i rest (by simpa [Kids.find] using h)
end

theorem absent_iff (t : PTrie) (key : List Nat) : AbsentWitness t key ↔ t.find key = some none :=
  ⟨absent_find, absent_of_find t key⟩

/-! ## Insertion along a witness -/

/-- Put child `c` into slot `n`. -/
def Kids.put : Kids → Nat → PTrie → Kids
  | .nil, _, _ => .nil
  | .none r, 0, c => .some c r
  | .some _ r, 0, c => .some c r
  | .none r, i + 1, c => .none (Kids.put r i c)
  | .some d r, i + 1, c => .some d (Kids.put r i c)

/-- Number of slots. -/
def Kids.len : Kids → Nat
  | .nil => 0
  | .none r => 1 + Kids.len r
  | .some _ r => 1 + Kids.len r

theorem Kids.len_of_wf : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → Kids.len cs = n
  | .nil, n, h => by simp [Kids.wf] at h; simp [Kids.len, h]
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp [Kids.len, Kids.len_of_wf r _ h.2]; omega
  | .some _ r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp [Kids.len, Kids.len_of_wf r _ h.2]; omega

theorem Kids.upsert_empty : ∀ (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes),
    n < Kids.len cs → Kids.slot cs n = none →
    Kids.upsert cs n key v = some (Kids.put cs n (newLeaf key v), 0, leafMem key v.length)
  | .nil, _, _, _, h, _ => by simp [Kids.len] at h
  | .none _, 0, _, _, _, _ => by simp [Kids.upsert, Kids.put, newLeaf]
  | .some _ _, 0, _, _, _, h => by simp [Kids.slot] at h
  | .none r, i + 1, key, v, hl, hs => by
    simp only [Kids.upsert, Kids.put]
    rw [Kids.upsert_empty r i key v (by simp [Kids.len] at hl; omega) (by simpa [Kids.slot] using hs)]
    rfl
  | .some _ r, i + 1, key, v, hl, hs => by
    simp only [Kids.upsert, Kids.put]
    rw [Kids.upsert_empty r i key v (by simp [Kids.len] at hl; omega) (by simpa [Kids.slot] using hs)]
    rfl

theorem Kids.upsert_down : ∀ (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes) (c c' : PTrie) (cm : Nat),
    Kids.slot cs n = some c → c.mem? = some cm → c.upsert key v = some c' →
    Kids.upsert cs n key v = some (Kids.put cs n c', cm, c'.memD)
  | .nil, _, _, _, _, _, _, h, _, _ => by simp [Kids.slot] at h
  | .none _, 0, _, _, _, _, _, h, _, _ => by simp [Kids.slot] at h
  | .some d _, 0, key, v, c, c', cm, h, hm, hu => by
    simp [Kids.slot] at h; subst h; simp [Kids.upsert, Kids.put, hm, hu]
  | .none r, i + 1, key, v, c, c', cm, h, hm, hu => by
    simp only [Kids.upsert, Kids.put]
    rw [Kids.upsert_down r i key v c c' cm (by simpa [Kids.slot] using h) hm hu]; rfl
  | .some _ r, i + 1, key, v, c, c', cm, h, hm, hu => by
    simp only [Kids.upsert, Kids.put]
    rw [Kids.upsert_down r i key v c c' cm (by simpa [Kids.slot] using h) hm hu]; rfl

/-- `ABS_BR`: a new leaf in the empty slot; the branch gains the leaf's usage. -/
theorem upsert_brSlot {bv : Option Slot} {cs : Kids} {m n : Nat} {rest : List Nat} {v : Bytes}
    (hw : Kids.wf cs 16 = true) (hn : n < 16) (hs : Kids.slot cs n = none) :
    (PTrie.branch bv cs m).upsert (n :: rest) v =
      some (.branch bv (Kids.put cs n (newLeaf rest v)) (m + leafMem rest v.length)) := by
  simp [PTrie.upsert, Kids.upsert_empty cs n rest v (by rw [Kids.len_of_wf cs 16 hw]; exact hn) hs]

/-- `ABS_VAL`: the branch gains the value. -/
theorem upsert_brVal {cs : Kids} {m : Nat} {v : Bytes} :
    (PTrie.branch none cs m).upsert [] v = some (.branch (some (.val v)) cs (m + valueMem v.length)) := by
  simp [PTrie.upsert]

/-- `ABS_KEY` at a leaf: the leaf is split. -/
theorem upsert_leaf_ne {k : List Nat} {s : Slot} {m : Nat} {key : List Nat} {v : Bytes} (h : k ≠ key) :
    (PTrie.leaf k s m).upsert key v = some (splitLeaf k s key v) := by
  simp [PTrie.upsert, h]

/-- `ABS_KEY` at an extension: the extension is split. -/
theorem upsert_ext_np {k : List Nat} {c : PTrie} {m : Nat} {key : List Nat} {v : Bytes}
    (h : isPrefix k key = false) : (PTrie.ext k c m).upsert key v = some (splitExt k c m key v) := by
  simp [PTrie.upsert, h]

/-- A step down a branch: the child is replaced, the branch usage moves by the child's change. -/
theorem upsert_branch_down {bv : Option Slot} {cs : Kids} {m n : Nat} {rest : List Nat} {v : Bytes}
    {c c' : PTrie} {cm : Nat} (hs : Kids.slot cs n = some c) (hm : c.mem? = some cm)
    (hu : c.upsert rest v = some c') :
    (PTrie.branch bv cs m).upsert (n :: rest) v =
      some (.branch bv (Kids.put cs n c') (m + c'.memD - cm)) := by
  simp [PTrie.upsert, Kids.upsert_down cs n rest v c c' cm hs hm hu]

/-- A step down an extension. -/
theorem upsert_ext_down {k : List Nat} {c c' : PTrie} {m cm : Nat} {key : List Nat} {v : Bytes}
    (hp : isPrefix k key = true) (hm : c.mem? = some cm) (hu : c.upsert (key.drop k.length) v = some c') :
    (PTrie.ext k c m).upsert key v = some (.ext k c' (m + c'.memD - cm)) := by
  simp [PTrie.upsert, hp, hm, hu]

theorem absent_isNode {t : PTrie} {key : List Nat} (h : AbsentWitness t key) : ∃ m, t.mem? = some m := by
  cases h <;> exact ⟨_, rfl⟩

theorem wf_kids_slot : ∀ (cs : Kids) (cnt n : Nat) (c : PTrie), Kids.wf cs cnt = true →
    Kids.slot cs n = some c → c.wf = true
  | .nil, _, _, _, _, h => by simp [Kids.slot] at h
  | .none _, _, 0, _, _, h => by simp [Kids.slot] at h
  | .some d _, _, 0, c, hw, h => by simp [Kids.slot] at h; subst h; exact (wf_kids_some hw).1
  | .none r, _, i + 1, c, hw, h => wf_kids_slot r _ i c (wf_kids_none hw) (by simpa [Kids.slot] using h)
  | .some _ r, _, i + 1, c, hw, h => wf_kids_slot r _ i c (wf_kids_some hw).2 (by simpa [Kids.slot] using h)

theorem slot_lt : ∀ (cs : Kids) (n : Nat) (c : PTrie), Kids.slot cs n = some c → n < Kids.len cs
  | .nil, _, _, h => by simp [Kids.slot] at h
  | .none _, 0, _, h => by simp [Kids.slot] at h
  | .some _ _, 0, _, _ => by simp [Kids.len]; omega
  | .none r, i + 1, c, h => by
    have := slot_lt r i c (by simpa [Kids.slot] using h); simp [Kids.len]; omega
  | .some _ r, i + 1, c, h => by
    have := slot_lt r i c (by simpa [Kids.slot] using h); simp [Kids.len]; omega

/-- **Insertion**: along an absence witness `upsert` succeeds; the new key maps
to `v`, every other key is unchanged. -/
theorem upsert_absent {t : PTrie} {key : List Nat} (h : AbsentWitness t key) (v : Bytes)
    (hw : t.wf = true) (hk : nibblesOk key = true) :
    ∃ t', t.upsert key v = some t' ∧ t'.find key = some (some v) ∧
      ∀ k', k' ≠ key → t'.find k' = t.find k' := by
  have hex : ∃ t', t.upsert key v = some t' := by
    induction h with
    | brSlot hs =>
      rename_i bv cs m n rest
      have hcw := wf_branch hw
      have hn : n < 16 := (nibblesOk_cons.1 hk).1
      exact ⟨_, upsert_brSlot hcw hn hs⟩
    | brVal => exact ⟨_, upsert_brVal⟩
    | brDown hs hc ih =>
      obtain ⟨c', hc'⟩ := ih (wf_kids_slot _ _ _ _ (wf_branch hw) hs) (nibblesOk_cons.1 hk).2
      obtain ⟨cm, hm⟩ := absent_isNode hc
      exact ⟨_, upsert_branch_down hs hm hc'⟩
    | extDown hp hc ih =>
      obtain ⟨c', hc'⟩ := ih (wf_ext hw).2 (nibblesOk_drop _ hk)
      obtain ⟨cm, hm⟩ := absent_isNode hc
      exact ⟨_, upsert_ext_down hp hm hc'⟩
    | extNib ha hb hab => exact ⟨_, upsert_ext_np (not_prefix_of_nib ha hb hab)⟩
    | extLen hl => exact ⟨_, upsert_ext_np (not_prefix_of_len hl)⟩
    | leafNib ha hb hab => exact ⟨_, upsert_leaf_ne (ne_of_nib ha hb hab)⟩
    | leafLen hl => exact ⟨_, upsert_leaf_ne (fun e => hl (by rw [e]))⟩
  obtain ⟨t', ht'⟩ := hex
  exact ⟨t', ht', PTrie.find_upsert_self t key v t' hk ht',
    fun k' hne => PTrie.find_upsert_other t key k' v t' hw hk hne ht'⟩

/-- `0x0f` (`TrieKey::BandwidthSchedulerState`) as nibbles. -/
theorem keyBwState_nibbles : NearSpecV3.keyBwState = [0, 15] := by decide

end ZkFormal.NearV3
