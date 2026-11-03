import StateM5a.StateView
import StateM5a.Ws

/-!
# StateM5a.StateViewParams — lane B's obligations of `StViewParams`, discharged (M5a-5)

`stViewParams_B E : StViewParams` is a concrete instance of every lane-B field of
`StateView.StViewParams`; lane E's choices are the explicit argument `E : StViewE`.
`stD_binding_B : Coll (stD (stViewParams_B E)) → Sha384Coll ∨ Sha256Coll ∨ LeafColl` and
`viewImpl_hst_B` (the `hst` premise of `viewImpl_binding_bad`) follow, for every `E`.

## The projection

The state lane's part of a component `v : StV` is its **overlay** `ovlOf v : Option Ovl` (the
receipt state's `o` at the positions `txs`/`locals`/`delayed`/`incoming`/`yields`; `none` at
`start`/`done`, `fin` and `none`). `strip v` is `v` with the overlay replaced by `blankOvl`;
`strip_ovl_inj`: `strip` and `ovlOf` determine `v`.

* `wsOfB E v = (E.keysOf v).map (entryAt o)`: per key, `(key, pre, cur, written)` with
  `pre = (o.trie.find (nibbles key)).getD none`, `cur`/`written` = the **committed** change
  (`kvFind key o.committed`), else `(pre, false)`. Prospective changes (`o.prosp`) are not in
  the entries; they are in the remainder.
* `trieOfB v = o.trie` (the partial trie; `.hash 0³²` without an overlay).
* `restOfB v = (strip v, (ovlOf v).map ovlRest)`, `ovlRest o = (erase o.trie, committed keys in
  order, o.prosp, o.cdRemovals)`; `encRestB = lp (E.encE ·) ‖ optEnc ovlRestEnc ·`.
* `fitsB E v`: the list fits the tree, values `< 2^24`, the trie is well-formed, `idxOf < 2^64`,
  and the overlay invariants `ovlInv` (committed keys distinct and all in `keysOf v`).
* `rawB E v = lp (E.encE (strip v)) ‖ optEnc ovlEnc (ovlOf v)` (the whole overlay).

## Proved (lane B)

* Encoders: `PF` (prefix-free) for `vnat` (LEB128), `lp`, pairs, lists, options, slots, and the
  full partial trie `tEnc`/`kEnc` (`tEnc_pf`); `ovlRestEnc_pf`, `ovlEnc_pf`.
* **`leafBlockN_inj`** (`leafBlock_inj`): `leafBlockN` is `Ws.leafBlock` at word level — word
  `t` has limbs `(pv_{2t}, pv_{2t+1}, kd_t + 2^16·x_t)` (`wlimbs_word`), `kd`/`pv`/`cv` the
  16-bit big-endian limbs of the 32-byte hashes (`be16`), `x_0 = pp + 2cp + 4wr`, `x_{1..4}` /
  `x_{5..8}` the 6-bit chunks of the two lengths. Injective on `WsLeaf.WF` (32-byte hashes,
  lengths `< 2^24`); the 16-bit and flag ranges hold by construction (`be16_lt`, `xs_lt`) and the
  per-limb step is `WsCost.leafLimb_inj`'s arithmetic (`hi_inj`, `word_fields`).
* **`encRestB_inj`** (`encRest_inj`), **`rawB_inj`** (`raw_inj`), **`rest_shapeB`**
  (`rest_shape`), **`proj_injB`** (`proj_inj`, through `kv_ext`: a list with distinct keys is
  determined by its key order and its lookups).

## What lane E must provide (`StViewE`) — the residual, exactly

1. **`encE` / `encE_inj`**: an encoder of stripped components with
   `∀ a b, encE (strip a) = encE (strip b) → strip a = strip b` — an injective encoding of the
   `EPos` (phase, remaining work lists, the receipt state's fields other than `o`: `limits`,
   `outgoing`, `bufIdx`, `metas`, `cong`, `dq`, `outcomes`, `gas`, …; `TxD2`, `Rcpt`, `MainOutD2`
   at `done`), the `Recording`, and `MainOutD2` at `fin`. The encoders above (`vnat`, `lp`,
   `listEnc`, `optEnc`, `pf_pair`) are the building blocks; only the spec record types are
   lane E's (M5b/M5d).
2. **`keysOf : StV → List Bytes`**: the working set's keys, in the circuit's leaf order. Binding
   needs **no** hypothesis on it (`ovlInv` is checked inside `fits`). For the circuit to compute
   `stD` it must be the chunk's key set — every key the chunk touches, including keys read or
   inserted only later — as a function of `StV`. That set is not determined by the overlay
   (future keys) nor by the partial trie (inserted keys are not revealed leaves), so lane E must
   **carry the chunk's key list in `StV`** (e.g. in the `eng` constructor, filled from the intake
   record), i.e. `keysOf (stOf c) = K(I)` for the run's intake `I`.
3. **`idxOf`**, **`depth`** (`< 64`; the circuit's `IX_BYTES = 3` needs `depth ≤ 24`).
4. **Not for binding** (segment soundness / completeness): every reached component is in the
   circuit form, `FitsReach E R : ∀ c, R c → fitsB E (stOf c) = true` for lane E's reachability
   predicate `R` on `EConf` (`fitsB_of` splits it): in particular the **trie obligation** that
   replaces M5a-4's `trie_ok`: `(o.trie).wf = true` and `o.trie = t` for the trie `t` the engine
   starts from (`Ovl.ofTrie t` in `preludeK`; the trie `INTAKE` reveals from the witness, never
   modified afterwards), whose `hashOf` is
   `prev_state_root` (`TCH`) and whose `erase` is the chunk-constant shape in `rest`; and
   `ovlInv`: committed keys distinct (kept by `kvPut`) and all in `keysOf`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StateM5a.StateViewParams

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E StateM5a.Walk StateM5a.SerInj StateM5a.StateView
open NearSpecV3.E2E.Bnd (StV ViewImpl Coll Sha384Coll bdigest eposMap stOf)

/-! ## Prefix-free byte encoders -/

/-- A prefix-free (hence injective) encoder: an encoding followed by anything determines the
value and the rest. -/
def PF {α : Type} (f : α → Bytes) : Prop :=
  ∀ a b (r r' : Bytes), f a ++ r = f b ++ r' → a = b ∧ r = r'

theorem PF.inj {α : Type} {f : α → Bytes} (h : PF f) {a b : α} (e : f a = f b) : a = b :=
  (h a b [] [] (by simpa using e)).1

/-- Unsigned LEB128: 7 bits per byte, high bit = continuation. -/
def vnat (n : Nat) : Bytes :=
  if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (128 + n % 128) :: vnat (n / 128)
termination_by n
decreasing_by omega

theorem vnat_eq (n : Nat) : vnat n =
    if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (128 + n % 128) :: vnat (n / 128) := by
  rw [vnat]

theorem vnat_pf : PF vnat := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro m r r' h
    rw [vnat_eq n, vnat_eq m] at h
    by_cases hn : n < 128 <;> by_cases hm : m < 128 <;>
      simp only [hn, hm, ite_true, ite_false, List.cons_append, List.nil_append, List.cons.injEq] at h
    · have := congrArg UInt8.toNat h.1
      rw [ofNat_toNat, ofNat_toNat] at this
      exact ⟨by omega, h.2⟩
    · have := congrArg UInt8.toNat h.1
      rw [ofNat_toNat, ofNat_toNat] at this
      omega
    · have := congrArg UInt8.toNat h.1
      rw [ofNat_toNat, ofNat_toNat] at this
      omega
    · have h1 := congrArg UInt8.toNat h.1
      rw [ofNat_toNat, ofNat_toNat] at h1
      obtain ⟨e, hr⟩ := ih (n / 128) (by omega) (m / 128) r r' h.2
      exact ⟨by omega, hr⟩

/-- A byte string with its length. -/
def lp (b : Bytes) : Bytes := vnat b.length ++ b

theorem lp_pf : PF lp := by
  intro a b r r' h
  simp only [lp, List.append_assoc] at h
  obtain ⟨hl, h51⟩ := vnat_pf _ _ _ _ h
  obtain ⟨rfl, rfl⟩ := List.append_inj h51 hl
  exact ⟨rfl, rfl⟩

theorem pf_pair {α β : Type} {f : α → Bytes} {g : β → Bytes} (hf : PF f) (hg : PF g) :
    PF (fun p : α × β => f p.1 ++ g p.2) := by
  intro ⟨a, b⟩ ⟨a', b'⟩ r r' h
  simp only [List.append_assoc] at h
  obtain ⟨rfl, h59⟩ := hf _ _ _ _ h
  obtain ⟨rfl, rfl⟩ := hg _ _ _ _ h59
  exact ⟨rfl, rfl⟩

/-- A list: `1 ‖ item` per element, then `0`. -/
def listEnc {α : Type} (f : α → Bytes) : List α → Bytes
  | [] => [0]
  | a :: l => 1 :: (f a ++ listEnc f l)

theorem listEnc_pf {α : Type} {f : α → Bytes} (hf : PF f) : PF (listEnc f) := by
  intro l
  induction l with
  | nil =>
    intro l' r r' h
    cases l' with
    | nil => exact ⟨rfl, by simpa [listEnc] using h⟩
    | cons => simp [listEnc] at h
  | cons a l ih =>
    intro l' r r' h
    cases l' with
    | nil => simp [listEnc] at h
    | cons a' l' =>
      simp only [listEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨rfl, h82⟩ := hf _ _ _ _ h
      obtain ⟨rfl, rfl⟩ := ih _ _ _ h82
      exact ⟨rfl, rfl⟩

/-- An option: `0`, or `1 ‖ value`. -/
def optEnc {α : Type} (f : α → Bytes) : Option α → Bytes
  | none => [0]
  | some a => 1 :: f a

theorem optEnc_pf {α : Type} {f : α → Bytes} (hf : PF f) : PF (optEnc f) := by
  intro a b r r' h
  cases a <;> cases b <;> simp only [optEnc, List.cons_append, List.nil_append, List.cons.injEq] at h
  · exact ⟨rfl, h.2⟩
  · simp at h
  · simp at h
  · obtain ⟨rfl, h97⟩ := hf _ _ _ _ h.2
    exact ⟨rfl, h97⟩

/-! ## The full encoding of a partial trie -/

def slotEnc : Slot → Bytes
  | .val v => 0 :: lp v
  | .ref l h => 1 :: (vnat l ++ lp h)

theorem slotEnc_pf : PF slotEnc := by
  intro a b r r' h
  cases a <;> cases b <;> simp only [slotEnc, List.cons_append, List.cons.injEq] at h
  · obtain ⟨rfl, h109⟩ := lp_pf _ _ _ _ h.2
    exact ⟨rfl, h109⟩
  · simp at h
  · simp at h
  · simp only [List.append_assoc, true_and] at h
    obtain ⟨rfl, h114⟩ := vnat_pf _ _ _ _ h
    obtain ⟨rfl, h115⟩ := lp_pf _ _ _ _ h114
    exact ⟨rfl, h115⟩

mutual
/-- Every constructor, key nibble, memory count, hash and value of a partial trie. -/
def tEnc : PTrie → Bytes
  | .hash h => 0 :: lp h
  | .leaf k s m => 1 :: (listEnc vnat k ++ slotEnc s ++ vnat m)
  | .ext k c m => 2 :: (listEnc vnat k ++ tEnc c ++ vnat m)
  | .branch v cs m => 3 :: (optEnc slotEnc v ++ kEnc cs ++ vnat m)
def kEnc : Kids → Bytes
  | .nil => [0]
  | .none r => 1 :: kEnc r
  | .some c r => 2 :: (tEnc c ++ kEnc r)
end

mutual
theorem tEnc_pf : ∀ (t t' : PTrie) (r r' : Bytes), tEnc t ++ r = tEnc t' ++ r' → t = t' ∧ r = r'
  | .hash h, .hash h', r, r', e => by
    simp only [tEnc, List.cons_append, List.cons.injEq, true_and] at e
    obtain ⟨rfl, e135⟩ := lp_pf _ _ _ _ e
    exact ⟨rfl, e135⟩
  | .leaf k s m, .leaf k' s' m', r, r', e => by
    simp only [tEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at e
    obtain ⟨rfl, e139⟩ := listEnc_pf vnat_pf _ _ _ _ e
    obtain ⟨rfl, e140⟩ := slotEnc_pf _ _ _ _ e139
    obtain ⟨rfl, e141⟩ := vnat_pf _ _ _ _ e140
    exact ⟨rfl, e141⟩
  | .ext k c m, .ext k' c' m', r, r', e => by
    simp only [tEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at e
    obtain ⟨rfl, e145⟩ := listEnc_pf vnat_pf _ _ _ _ e
    obtain ⟨rfl, e146⟩ := tEnc_pf c c' _ _ e145
    obtain ⟨rfl, e147⟩ := vnat_pf _ _ _ _ e146
    exact ⟨rfl, e147⟩
  | .branch v cs m, .branch v' cs' m', r, r', e => by
    simp only [tEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at e
    obtain ⟨rfl, e151⟩ := optEnc_pf slotEnc_pf _ _ _ _ e
    obtain ⟨rfl, e152⟩ := kEnc_pf cs cs' _ _ e151
    obtain ⟨rfl, e153⟩ := vnat_pf _ _ _ _ e152
    exact ⟨rfl, e153⟩
  | .hash _, .leaf .., _, _, e | .hash _, .ext .., _, _, e | .hash _, .branch .., _, _, e
  | .leaf .., .hash _, _, _, e | .leaf .., .ext .., _, _, e | .leaf .., .branch .., _, _, e
  | .ext .., .hash _, _, _, e | .ext .., .leaf .., _, _, e | .ext .., .branch .., _, _, e
  | .branch .., .hash _, _, _, e | .branch .., .leaf .., _, _, e
  | .branch .., .ext .., _, _, e => by simp [tEnc] at e
theorem kEnc_pf : ∀ (cs cs' : Kids) (r r' : Bytes), kEnc cs ++ r = kEnc cs' ++ r' →
    cs = cs' ∧ r = r'
  | .nil, .nil, r, r', e => by simpa [kEnc] using e
  | .none c, .none c', r, r', e => by
    simp only [kEnc, List.cons_append, List.cons.injEq, true_and] at e
    obtain ⟨rfl, e165⟩ := kEnc_pf c c' _ _ e
    exact ⟨rfl, e165⟩
  | .some c cs, .some c' cs', r, r', e => by
    simp only [kEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at e
    obtain ⟨rfl, e169⟩ := tEnc_pf c c' _ _ e
    obtain ⟨rfl, e170⟩ := kEnc_pf cs cs' _ _ e169
    exact ⟨rfl, e170⟩
  | .nil, .none _, _, _, e | .nil, .some .., _, _, e | .none _, .nil, _, _, e
  | .none _, .some .., _, _, e | .some .., .nil, _, _, e | .some .., .none _, _, _, e => by
    simp [kEnc] at e
end

/-! ## The leaf block (`Ws.leafBlock` at word level) and `leafBlock_inj` -/

/-- The `j`-th 16-bit big-endian limb of a byte string (`kd_j = 256·kb_{2j} + kb_{2j+1}`, as in
`WSL`). -/
def be16 (b : Bytes) (j : Nat) : Nat := 256 * (b.getD (2 * j) 0).toNat + (b.getD (2 * j + 1) 0).toNat

/-- A 64-bit word from the chip's limbs `[0,21) [21,42) [42,64)` (`wlimbs`). -/
def word (a b c : Nat) : Nat := a + 2097152 * b + 4398046511104 * c

/-- The side slots `x_t` (`Ws.leafX`): slot 0 = `pp + 2·cp + 4·wr`, slots 1–4 the pre-value
length's 6-bit chunks, 5–8 the current length's, 9–15 zero. -/
def xs (l : WsLeaf) (t : Nat) : Nat :=
  if t = 0 then l.pre.present.toNat + 2 * l.cur.present.toNat + 4 * l.wr.toNat
  else if t ≤ 4 then l.pre.len / 64 ^ (t - 1) % 64
  else if t ≤ 8 then l.cur.len / 64 ^ (t - 5) % 64
  else 0

/-- **The leaf block** (16 words, one SHA-512 block): word `t < 8` has limbs
`(pv_{2t}, pv_{2t+1}, kd_t + 2^16·x_t)`, word `8 + t` has `(cv_{2t}, cv_{2t+1}, kd_{8+t} + 2^16·x_{8+t})`
— `Ws.leafBlock` with `kd`, `pv`, `cv` the 16-bit big-endian limbs of the key hash and the two
value hashes. -/
def leafBlockN (l : WsLeaf) : List Nat :=
  (List.range 8).map (fun t => word (be16 l.pre.h (2 * t)) (be16 l.pre.h (2 * t + 1))
    (be16 l.kd t + 65536 * xs l t)) ++
  (List.range 8).map (fun t => word (be16 l.cur.h (2 * t)) (be16 l.cur.h (2 * t + 1))
    (be16 l.kd (8 + t) + 65536 * xs l (8 + t)))

theorem be16_lt (b : Bytes) (j : Nat) : be16 b j < 65536 := by
  have := (b.getD (2 * j) 0).toNat_lt; have := (b.getD (2 * j + 1) 0).toNat_lt
  simp only [be16]; omega

theorem xs_lt (l : WsLeaf) (t : Nat) : xs l t < 64 := by
  simp only [xs]
  have := l.pre.present.toNat_le; have := l.cur.present.toNat_le; have := l.wr.toNat_le
  repeat' split
  all_goals omega

/-- The chip's limbs of a word built from in-range limbs. -/
theorem wlimbs_word (a b c : Nat) (ha : a < 2 ^ 21) (hb : b < 2 ^ 21) :
    wlimbs (word a b c) = [a, b, c] := by
  simp only [wlimbs, word, List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega⟩

theorem word_inj {a b c a' b' c' : Nat} (ha : a < 2097152) (hb : b < 2097152)
    (ha' : a' < 2097152) (hb' : b' < 2097152)
    (h : word a b c = word a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  simp only [word] at h; omega

theorem hi_inj {k x k' x' : Nat} (hk : k < 65536) (hk' : k' < 65536)
    (h : k + 65536 * x = k' + 65536 * x') : k = k' ∧ x = x' := by omega

/-- One word of the block determines its three fields. -/
theorem word_fields {p q k x p' q' k' x' : Nat} (hp : p < 65536) (hq : q < 65536) (hk : k < 65536)
    (hp' : p' < 65536) (hq' : q' < 65536) (hk' : k' < 65536)
    (h : word p q (k + 65536 * x) = word p' q' (k' + 65536 * x')) :
    p = p' ∧ q = q' ∧ k = k' ∧ x = x' := by
  obtain ⟨h1, h2, h3⟩ := word_inj (by omega) (by omega) (by omega) (by omega) h
  obtain ⟨h4, h5⟩ := hi_inj hk hk' h3
  exact ⟨h1, h2, h4, h5⟩

/-- 32 bytes are determined by their 16 limbs. -/
theorem bytes_of_be16 (b b' : Bytes) (hl : b.length = 32) (hl' : b'.length = 32)
    (h : ∀ j < 16, be16 b j = be16 b' j) : b = b' := by
  apply List.ext_getElem (by rw [hl, hl'])
  intro i h1 h2
  have hj := h (i / 2) (by omega)
  simp only [be16] at hj
  have a0 := (b.getD (2 * (i / 2)) 0).toNat_lt; have a1 := (b.getD (2 * (i / 2) + 1) 0).toNat_lt
  have b0 := (b'.getD (2 * (i / 2)) 0).toNat_lt; have b1 := (b'.getD (2 * (i / 2) + 1) 0).toNat_lt
  have e0 : (b.getD (2 * (i / 2)) 0).toNat = (b'.getD (2 * (i / 2)) 0).toNat := by omega
  have e1 : (b.getD (2 * (i / 2) + 1) 0).toNat = (b'.getD (2 * (i / 2) + 1) 0).toNat := by omega
  have hi : b.getD i 0 = b'.getD i 0 := by
    obtain ⟨m, rfl | rfl⟩ : ∃ m, i = 2 * m ∨ i = 2 * m + 1 := ⟨i / 2, by omega⟩
    · have : 2 * m / 2 = m := by omega
      rw [this] at e0; exact UInt8.toNat_inj.mp e0
    · have : (2 * m + 1) / 2 = m := by omega
      rw [this] at e1; exact UInt8.toNat_inj.mp e1
  simpa [List.getD_eq_getElem?_getD, h1, h2] using hi

theorem bool_toNat_inj {a b : Bool} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

/-- **`leafBlock_inj`**: the leaf block is injective on well-formed leaves (32-byte hashes,
lengths `< 2^24`; the 16-bit limbs and the flag bits are in range by construction). -/
theorem leafBlockN_inj (a b : WsLeaf) (ha : a.WF) (hb : b.WF) (h : leafBlockN a = leafBlockN b) :
    a = b := by
  obtain ⟨ak, ⟨ap, apl⟩, ⟨ac, acl⟩⟩ := ha
  obtain ⟨bk, ⟨bp, bpl⟩, ⟨bc, bcl⟩⟩ := hb
  simp only [leafBlockN] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  rw [List.map_inj_left] at h1 h2
  have w1 : ∀ t < 8, be16 a.pre.h (2 * t) = be16 b.pre.h (2 * t) ∧
      be16 a.pre.h (2 * t + 1) = be16 b.pre.h (2 * t + 1) ∧ be16 a.kd t = be16 b.kd t ∧
      xs a t = xs b t := fun t ht =>
    word_fields (be16_lt _ _) (be16_lt _ _) (be16_lt _ _) (be16_lt _ _) (be16_lt _ _)
      (be16_lt _ _) (h1 t (List.mem_range.mpr ht))
  have w2 : ∀ t < 8, be16 a.cur.h (2 * t) = be16 b.cur.h (2 * t) ∧
      be16 a.cur.h (2 * t + 1) = be16 b.cur.h (2 * t + 1) ∧ be16 a.kd (8 + t) = be16 b.kd (8 + t) ∧
      xs a (8 + t) = xs b (8 + t) := fun t ht =>
    word_fields (be16_lt _ _) (be16_lt _ _) (be16_lt _ _) (be16_lt _ _) (be16_lt _ _)
      (be16_lt _ _) (h2 t (List.mem_range.mpr ht))
  have hkd : a.kd = b.kd := bytes_of_be16 _ _ ak bk fun j hj => by
    rcases Nat.lt_or_ge j 8 with hj8 | hj8
    · exact (w1 j hj8).2.2.1
    · have := (w2 (j - 8) (by omega)).2.2.1
      rwa [show 8 + (j - 8) = j by omega] at this
  have hph : a.pre.h = b.pre.h := bytes_of_be16 _ _ ap bp fun j hj => by
    obtain ⟨m, rfl | rfl⟩ : ∃ m, j = 2 * m ∨ j = 2 * m + 1 := ⟨j / 2, by omega⟩
    · exact (w1 m (by omega)).1
    · exact (w1 m (by omega)).2.1
  have hch : a.cur.h = b.cur.h := bytes_of_be16 _ _ ac bc fun j hj => by
    obtain ⟨m, rfl | rfl⟩ : ∃ m, j = 2 * m ∨ j = 2 * m + 1 := ⟨j / 2, by omega⟩
    · exact (w2 m (by omega)).1
    · exact (w2 m (by omega)).2.1
  have x0 := (w1 0 (by omega)).2.2.2
  have x1 := (w1 1 (by omega)).2.2.2
  have x2 := (w1 2 (by omega)).2.2.2
  have x3 := (w1 3 (by omega)).2.2.2
  have x4 := (w1 4 (by omega)).2.2.2
  have x5 := (w1 5 (by omega)).2.2.2
  have x6 := (w1 6 (by omega)).2.2.2
  have x7 := (w1 7 (by omega)).2.2.2
  have x8 := (w2 0 (by omega)).2.2.2
  simp only [xs, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceLeDiff, Nat.reduceEqDiff,
    ite_true, ite_false, Nat.div_one] at x0 x1 x2 x3 x4 x5 x6 x7 x8
  have := a.pre.present.toNat_le; have := a.cur.present.toNat_le; have := a.wr.toNat_le
  have := b.pre.present.toNat_le; have := b.cur.present.toNat_le; have := b.wr.toNat_le
  have hpp := bool_toNat_inj (a := a.pre.present) (b := b.pre.present) (by omega)
  have hcp := bool_toNat_inj (a := a.cur.present) (b := b.cur.present) (by omega)
  have hwr := bool_toNat_inj (a := a.wr) (b := b.wr) (by omega)
  have hpl : a.pre.len = b.pre.len := by simp only [Nat.reducePow] at apl bpl; omega
  have hcl : a.cur.len = b.cur.len := by simp only [Nat.reducePow] at acl bcl; omega
  obtain ⟨akd, ⟨app, apln, aph⟩, ⟨acp, acln, ach⟩, awr⟩ := a
  obtain ⟨bkd, ⟨bpp, bpln, bph⟩, ⟨bcp, bcln, bch⟩, bwr⟩ := b
  simp_all

/-! ## The overlay of a state component -/

/-- The overlay of an engine position (the positions that carry a receipt state). -/
def posOvl : EPos → Option Ovl
  | .txs _ _ rs | .locals _ rs | .delayed _ rs | .incoming _ rs | .yields _ _ _ _ _ rs => some rs.o
  | _ => none

def setO (o : Ovl) (rs : RS) : RS := { rs with o := o }

/-- The overlay of a state component (`none` at `start`/`done`, `fin` and `none`). -/
def ovlOf : StV → Option Ovl
  | .eng p _ => posOvl p
  | _ => none

/-- Replace the overlay (identity where there is none). -/
def setOvl (o : Ovl) : StV → StV
  | .eng p st => .eng (eposMap (setO o) p) st
  | v => v

def blankOvl : Ovl := ⟨.hash [], [], [], 0⟩

/-- **The stripped component**: the overlay blanked out. Everything lane E encodes. -/
def strip (v : StV) : StV := setOvl blankOvl v

theorem setO_self (rs : RS) : setO rs.o rs = rs := by cases rs; rfl
theorem setO_setO (o o' : Ovl) (rs : RS) : setO o' (setO o rs) = setO o' rs := by cases rs; rfl

theorem setOvl_self (o : Ovl) (v : StV) (h : ovlOf v = some o) : setOvl o v = v := by
  cases v with
  | eng p st =>
    cases p <;> simp only [ovlOf, posOvl, reduceCtorEq, Option.some.injEq] at h <;>
      subst h <;> simp only [setOvl, eposMap, setO_self]
  | _ => rfl

theorem setOvl_none (o : Ovl) (v : StV) (h : ovlOf v = none) : setOvl o v = v := by
  cases v with
  | eng p st => cases p <;> simp_all [ovlOf, posOvl, setOvl, eposMap]
  | _ => rfl

theorem setOvl_setOvl (o o' : Ovl) (v : StV) : setOvl o' (setOvl o v) = setOvl o' v := by
  cases v with
  | eng p st => cases p <;> simp only [setOvl, eposMap, setO_setO]
  | _ => rfl

theorem ovlOf_setOvl (o : Ovl) (v : StV) : ovlOf (setOvl o v) = (ovlOf v).map fun _ => o := by
  cases v with
  | eng p st => cases p <;> rfl
  | _ => rfl

/-- The stripped component and the overlay determine the state component. -/
theorem strip_ovl_inj (a b : StV) (hs : strip a = strip b) (ho : ovlOf a = ovlOf b) : a = b := by
  cases h : ovlOf a with
  | none =>
    rw [h] at ho
    rw [← setOvl_none blankOvl a h, ← setOvl_none blankOvl b ho.symm]; exact hs
  | some o =>
    rw [h] at ho
    rw [← setOvl_self o a h, ← setOvl_self o b ho.symm, ← setOvl_setOvl blankOvl o a,
      ← setOvl_setOvl blankOvl o b]
    exact congrArg (setOvl o) hs

/-! ## Overlay lists -/

theorem kvFind_cons (k k' : Bytes) (v : Option Bytes) (r : List (Bytes × Option Bytes)) :
    kvFind k ((k', v) :: r) = if k' = k then some v else kvFind k r := by
  simp only [kvFind, beq_iff_eq]

theorem kvFind_mem : ∀ (k : Bytes) (l : List (Bytes × Option Bytes)) (x : Option Bytes),
    kvFind k l = some x → k ∈ l.map Prod.fst
  | _, [], _, h => by simp [kvFind] at h
  | k, (k', v) :: r, x, h => by
    rw [kvFind_cons] at h
    by_cases e : k' = k
    · simp [e]
    · simp only [e, ite_false] at h
      exact List.mem_cons_of_mem _ (kvFind_mem k r x h)

theorem kvFind_none : ∀ (k : Bytes) (l : List (Bytes × Option Bytes)),
    k ∉ l.map Prod.fst → kvFind k l = none
  | _, [], _ => rfl
  | k, (k', v) :: r, h => by
    have hne : ¬ k' = k := fun e => h (by simp [e])
    simp only [kvFind_cons, hne, ite_false]
    exact kvFind_none k r (fun hm => h (List.mem_cons_of_mem _ hm))

/-- An overlay list with distinct keys is determined by its key order and its lookups. -/
theorem kv_ext : ∀ (l l' : List (Bytes × Option Bytes)), l.map Prod.fst = l'.map Prod.fst →
    (l.map Prod.fst).Nodup → (∀ k, kvFind k l = kvFind k l') → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | (k, v) :: r, (k', v') :: r', hk, hn, hf => by
    simp only [List.map_cons, List.cons.injEq] at hk
    obtain ⟨rfl, hk⟩ := hk
    simp only [List.map_cons, List.nodup_cons] at hn
    have hv := hf k
    simp only [kvFind_cons, ite_true, Option.some.injEq] at hv
    subst hv
    have hr : r = r' := kv_ext r r' hk hn.2 fun k2 => by
      by_cases e : k = k2
      · subst e
        rw [kvFind_none _ _ hn.1, kvFind_none _ _ (hk ▸ hn.1)]
      · have := hf k2
        simpa only [kvFind_cons, e, ite_false] using this
    rw [hr]

/-! ## The working set -/

/-- The pre-state value of a key (from the overlay's trie; `none` if absent or unrevealed). -/
def preV (o : Ovl) (k : Bytes) : Option Bytes := (o.trie.find (nibbles k)).getD none

/-- **A working-set entry** of an overlay: key, pre-state value, current committed value and
`written` = the key has a committed change. Prospective changes are not in the entry (they are
in the remainder). -/
def entryAt (o : Ovl) (k : Bytes) : Entry :=
  match kvFind k o.committed with
  | some x => (k, preV o k, x, true)
  | none => (k, preV o k, preV o k, false)

theorem entryAt_key (o : Ovl) (k : Bytes) : (entryAt o k).1 = k := by
  unfold entryAt; split <;> rfl

theorem entryAt_find (o o' : Ovl) (k : Bytes) (h : entryAt o k = entryAt o' k) :
    kvFind k o.committed = kvFind k o'.committed := by
  unfold entryAt at h
  split at h <;> split at h <;> simp_all

def zero32 : Bytes := List.replicate 32 0

/-! ## Lane E's part -/

/-- **What lane E provides** to the state view: the tree depth, the working set's key list, the
change index, and an encoder of the stripped component (`strip`: the `StV` with its overlay
blanked — position, the receipt state's other fields, `Recording`, `MainOutD2`) that is injective
on stripped components. -/
structure StViewE where
  depth : Nat
  depth_lt : depth < 64
  /-- the working set's keys (lane E: the chunk's key set, as a function of the component) -/
  keysOf : StV → List Bytes
  /-- the change index -/
  idxOf : StV → Nat
  /-- the stripped component's encoder -/
  encE : StV → Bytes
  encE_inj : ∀ a b, encE (strip a) = encE (strip b) → strip a = strip b

variable (E : StViewE)

/-- The working set of a component: one entry per key of `keysOf`. -/
def wsOfB (v : StV) : List Entry :=
  match ovlOf v with
  | some o => (E.keysOf v).map (entryAt o)
  | none => []

/-- The trie of a component: the overlay's partial trie itself (no expansion). -/
def trieOfB (v : StV) : PTrie :=
  match ovlOf v with
  | some o => o.trie
  | none => .hash zero32

/-- The overlay's part of the remainder: the trie's reveal shape, the committed keys in their
order, the prospective changes and the removal count. -/
abbrev OvlRest := PTrie × List Bytes × List (Bytes × Option Bytes) × Nat

def ovlRest (o : Ovl) : OvlRest := (erase o.trie, o.committed.map Prod.fst, o.prosp, o.cdRemovals)

/-- **The remainder**: the stripped component and the overlay's part. -/
abbrev RestB := StV × Option OvlRest

def restOfB (v : StV) : RestB := (strip v, (ovlOf v).map ovlRest)

def kvEnc (p : Bytes × Option Bytes) : Bytes := lp p.1 ++ optEnc lp p.2

theorem kvEnc_pf : PF kvEnc := pf_pair lp_pf (optEnc_pf lp_pf)

def ovlRestEnc (p : OvlRest) : Bytes :=
  tEnc p.1 ++ (listEnc lp p.2.1 ++ (listEnc kvEnc p.2.2.1 ++ vnat p.2.2.2))

theorem ovlRestEnc_pf : PF ovlRestEnc :=
  pf_pair tEnc_pf (pf_pair (listEnc_pf lp_pf) (pf_pair (listEnc_pf kvEnc_pf) vnat_pf))

/-- **The remainder's encoder.** -/
def encRestB (r : RestB) : Bytes := lp (E.encE r.1) ++ optEnc ovlRestEnc r.2

/-- The whole overlay (for the raw form). -/
def ovlEnc (o : Ovl) : Bytes :=
  tEnc o.trie ++ (listEnc kvEnc o.committed ++ (listEnc kvEnc o.prosp ++ vnat o.cdRemovals))

theorem ovlEnc_pf : PF ovlEnc := by
  intro ⟨t, c, p, n⟩ ⟨t', c', p', n'⟩ r r' h
  obtain ⟨e, hr⟩ := pf_pair tEnc_pf (pf_pair (listEnc_pf kvEnc_pf)
    (pf_pair (listEnc_pf kvEnc_pf) vnat_pf)) (t, c, p, n) (t', c', p', n') r r' h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  exact ⟨rfl, hr⟩

/-- **The raw form**: the stripped component and the whole overlay. -/
def rawB (v : StV) : Bytes := lp (E.encE (strip v)) ++ optEnc ovlEnc (ovlOf v)

def okB : Option Bytes → Bool
  | none => true
  | some x => decide (x.length < 2 ^ 24)

theorem okB_ok (v : Option Bytes) (h : okB v = true) : OptOk v := by
  intro x hx; subst hx; simpa [okB] using h

/-- The working-set invariants of an overlay: committed keys distinct and all in `keysOf`. -/
def ovlInv (v : StV) : Bool :=
  match ovlOf v with
  | some o => decide (o.committed.map Prod.fst).Nodup &&
      o.committed.all fun p => decide (p.1 ∈ E.keysOf v)
  | none => true

/-- **The circuit form applies.** -/
def fitsB (v : StV) : Bool :=
  decide ((wsOfB E v).length ≤ 2 ^ E.depth) &&
    (wsOfB E v).all (fun e => okB e.2.1 && okB e.2.2.1) && (trieOfB v).wf &&
    decide (E.idxOf v < 2 ^ 64) && ovlInv E v

theorem fitsB_parts {v : StV} (h : fitsB E v = true) :
    (wsOfB E v).length ≤ 2 ^ E.depth ∧ (∀ e ∈ wsOfB E v, e.Ok) ∧ (trieOfB v).wf = true ∧
      E.idxOf v < 2 ^ 64 ∧ ovlInv E v = true := by
  simp only [fitsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, fun e he => ⟨okB_ok _ (h2 e he).1, okB_ok _ (h2 e he).2⟩, h3, h4, h5⟩

/-- Build `fitsB` from its parts (lane E's reachability invariant, item 4 of the module doc). -/
theorem fitsB_of {v : StV} (h1 : (wsOfB E v).length ≤ 2 ^ E.depth)
    (h2 : ∀ e ∈ wsOfB E v, okB e.2.1 = true ∧ okB e.2.2.1 = true) (h3 : (trieOfB v).wf = true)
    (h4 : E.idxOf v < 2 ^ 64) (h5 : ovlInv E v = true) : fitsB E v = true := by
  simp only [fitsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

/-- Every configuration of lane E's reachability predicate `R` has its state component in the
circuit form (not needed for binding; the segment-soundness side of the state view). -/
def FitsReach (R : EConf → Prop) : Prop := ∀ c, R c → fitsB E (stOf c) = true

theorem ovlInv_parts {v : StV} {o : Ovl} (h : ovlInv E v = true) (ho : ovlOf v = some o) :
    (o.committed.map Prod.fst).Nodup ∧ ∀ k ∈ o.committed.map Prod.fst, k ∈ E.keysOf v := by
  simp only [ovlInv, ho, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, fun k hk => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  exact h.2 p hp

theorem encRestB_inj (a b : StV) (h : encRestB E (restOfB a) = encRestB E (restOfB b)) :
    restOfB a = restOfB b := by
  simp only [encRestB, restOfB] at h
  obtain ⟨h1, h2⟩ := lp_pf _ _ _ _ h
  have := E.encE_inj a b h1
  rw [restOfB, restOfB, this, (optEnc_pf ovlRestEnc_pf).inj h2]

theorem rawB_inj (a b : StV) (h : rawB E a = rawB E b) : a = b := by
  simp only [rawB] at h
  obtain ⟨h1, h2⟩ := lp_pf _ _ _ _ h
  exact strip_ovl_inj a b (E.encE_inj a b h1) ((optEnc_pf ovlEnc_pf).inj h2)

theorem rest_shapeB (a b : StV) (h : restOfB a = restOfB b) :
    erase (trieOfB a) = erase (trieOfB b) := by
  simp only [restOfB, Prod.mk.injEq] at h
  have h2 := h.2
  unfold trieOfB
  cases ha : ovlOf a <;> cases hb : ovlOf b <;> simp only [ha, hb, Option.map] at h2 ⊢
  · simp at h2
  · simp at h2
  · simp only [Option.some.injEq, ovlRest, Prod.mk.injEq] at h2
    exact h2.1

/-- **`proj_inj`** for the concrete projection: working set, trie and remainder determine the
component, on `fits` states (the overlay invariants `ovlInv` are part of `fits`). -/
theorem proj_injB (a b : StV) (fa : fitsB E a = true) (fb : fitsB E b = true)
    (hw : wsOfB E a = wsOfB E b) (ht : trieOfB a = trieOfB b) (hr : restOfB a = restOfB b) :
    a = b := by
  simp only [restOfB, Prod.mk.injEq] at hr
  obtain ⟨hs, ho⟩ := hr
  apply strip_ovl_inj a b hs
  unfold wsOfB at hw
  unfold trieOfB at ht
  cases ha : ovlOf a with
  | none => cases hb : ovlOf b with
    | none => rfl
    | some => simp [ha, hb] at ho
  | some oa => cases hb : ovlOf b with
    | none => simp [ha, hb] at ho
    | some ob =>
      simp only [ha, hb, Option.map, Option.some.injEq, ovlRest, Prod.mk.injEq] at ho ht hw
      obtain ⟨-, hk, hp, hc⟩ := ho
      have hK : E.keysOf a = E.keysOf b := by
        have := congrArg (List.map Prod.fst) hw
        simpa only [List.map_map, Function.comp_def, entryAt_key, List.map_id'] using this
      rw [hK, List.map_inj_left] at hw
      obtain ⟨na, ca⟩ := ovlInv_parts E (fitsB_parts E fa).2.2.2.2 ha
      obtain ⟨nb, cb⟩ := ovlInv_parts E (fitsB_parts E fb).2.2.2.2 hb
      have hcm : oa.committed = ob.committed := kv_ext _ _ hk na fun k => by
        by_cases hm : k ∈ E.keysOf b
        · exact entryAt_find _ _ _ (hw k hm)
        · rw [kvFind_none _ _ (fun h => hm (hK ▸ ca k h)), kvFind_none _ _ (fun h => hm (cb k h))]
      cases oa; cases ob
      simp_all

/-- **The state lane's instance of `StViewParams`**: every lane-B obligation proved; lane E
supplies `E` (`keysOf`, `idxOf`, `encE` with `encE_inj`). -/
def stViewParams_B : StViewParams where
  depth := E.depth
  depth_lt := E.depth_lt
  wsOf := wsOfB E
  trieOf := trieOfB
  idxOf := E.idxOf
  Rest := RestB
  restOf := restOfB
  encRest := encRestB E
  leafBlock := leafBlockN
  leafBlock_inj := leafBlockN_inj
  fits := fitsB E
  fits_ws_len := fun _ h => (fitsB_parts E h).1
  fits_ws_ok := fun _ h => (fitsB_parts E h).2.1
  fits_trie := fun _ h => (fitsB_parts E h).2.2.1
  fits_idx := fun _ h => (fitsB_parts E h).2.2.2.1
  raw := rawB E
  raw_inj := fun a b _ _ h => rawB_inj E a b h
  encRest_inj := fun a b _ _ h => encRestB_inj E a b h
  rest_shape := fun a b _ _ h => rest_shapeB a b h
  proj_inj := fun a b fa fb _ hw ht _ hr => proj_injB E a b fa fb hw ht hr

/-- **The state commitment's binding lemma, lane B's obligations discharged.** -/
theorem stD_binding_B (h : Coll (stD (stViewParams_B E))) : Sha384Coll ∨ Sha256Coll ∨ LeafColl :=
  stD_binding _ h

/-- The `hst` premise of `viewImpl_binding_bad` for the concrete instance. -/
theorem viewImpl_hst_B (V : ViewImpl) (hV : V.stD = stD (stViewParams_B E)) (Bad : Prop)
    (hsha : Sha384Coll → Bad) (h256 : Sha256Coll → Bad) (hleaf : LeafColl → Bad) :
    Coll V.stD → Bad :=
  viewImpl_hst _ V hV Bad hsha h256 hleaf

end StateM5a.StateViewParams
