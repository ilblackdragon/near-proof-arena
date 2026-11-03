import NearSpecV3.E2E.View
import StateM5a.SerInj
import StateM5a.Merkle

/-!
# StateM5a.StateView — the state component `stD` of lane E's `ViewImpl` (M5a-4 item 4)

`NearSpecV3.E2E.Bnd.ViewImpl` has one commitment function per configuration component; the
state component is `stD : StV → Bytes`, and `viewImpl_binding_bad` needs `Coll V.stD → Bad`.
This file fixes the **shape** of the state lane's `stD`, proves its binding modulo named hash
collisions, and names every obligation it cannot discharge yet as a field of `StViewParams`.

## The shape

A state commitment is the record `StCommit`:

| field | width | value (`commitOf P v`) |
|---|---|---|
| `tag` | 1 B | the `StV` constructor (`none` 0, `eng` 1, `fin` 2), `tagOf` |
| `ws` | 48 B | the working-set root (`RCH`): `wsRoot P (P.wsOf v)` |
| `wsLen` | `u64` | the number of working-set entries `(P.wsOf v).length` |
| `trie` | 32 B | the trie root (`TCH`): `(P.trieOf v).hashOf` (SHA-256, `RawTrieNodeWithSize`) |
| `idx` | `u64` | the change index `P.idxOf v` |
| `rest` | 42 B | `bdigest (P.encRest (P.restOf v))`: everything the three state-lane parts do not cover |

`ser c = [tag] ‖ ws ‖ u64 wsLen ‖ trie ‖ u64 idx ‖ rest` (fixed widths, 139 bytes), and
`stD P v = bdigest (ser (commitOf P v))`.

**The working-set root.** The working set is a list of plain entries `(key, pre, cur, written)`
(`Entry`; values `Option Bytes`, `none` = absent). Each entry becomes a circuit leaf
`leafOf e = (sha256 key, vref pre, vref cur, written)` with `vref (some x) = (1, |x|, sha256 x)`,
`vref none = (0, 0, 0³²)`; the leaf digest is `leafD P e = cmp384 (P.leafBlock (leafOf e))`, the
first 48 bytes of one SHA-512 compression from the SHA-384 IV (`cmp384`, as in `Ws.leafBlock`).
The tree has the fixed depth `P.depth`; leaves `≥ n` are the zero digest `0⁴⁸`; an inner node is
`nodeH l r = sha384 (l ‖ r)` (`Ws.nodeBlock`); `wsRoot P es` is `Merkle.root nodeH P.depth` of the
`2^depth` leaf digests.

## Proved here

* `ser_inj` — the serialization is injective on well-formed records (`StCommit.WF`);
  `commitOf_wf` — every `commitOf P v` is well-formed.
* `merkle_binding` — equal roots of two depth-`D` trees of 48-byte digests have equal leaves,
  or there is a `Sha384Coll` (a `nodeH` collision on 96-byte inputs is a full SHA-384 collision,
  hence a collision of its 42-byte truncation `bdigest`).
* `trie_binding` — two fully revealed (`Rev`: no hash stub, every value slot revealed),
  well-formed tries with the same `hashOf` are equal, or there is a `Sha256Coll`
  (through `SerInj.nodeSerInj` applied to the one-level stubbed node `shal t`).
* `leafOf_inj` — `leafOf` is injective modulo `Sha256Coll`.
* `wsRoot_binding` — equal working-set roots and lengths give equal entry lists, modulo
  `Sha384Coll ∨ Sha256Coll ∨ LeafColl`.
* `stD_binding` — `Coll (stD P) → Sha384Coll ∨ Sha256Coll ∨ LeafColl`; `stD_binding_bad` the
  same into a caller's `Bad`; `viewImpl_hst` — for any `V : ViewImpl` with `V.stD = stD P`,
  `Coll V.stD → Bad`: exactly the `hst` premise of `viewImpl_binding_bad`;
  `viewImpl_binding_st` — `viewImpl_binding_bad` with it plugged in.

## Named collision events (the only cryptographic content)

* `Sha384Coll` (lane E's, `View.lean`): a 42-byte `bdigest` collision; covers the outer digest,
  the `rest` digest and the working-set inner nodes.
* `Sha256Coll`: a SHA-256 collision; covers the trie nodes, trie values and the leaf's key /
  value hashes.
* `LeafColl`: a collision of `cmp384` (the truncated SHA-512 compression from `IV384` on one
  block), the working-set leaf digest.

## Parameters (`StViewParams`): obligations for later milestones

* `wsOf`, `trieOf`, `idxOf`, `Rest`/`restOf`: the projection of `StV` onto the three state-lane
  parts and the remainder. **`proj_inj`**: tag, working set, trie, index and remainder together
  determine the `StV` (lane E / M5b: the choice of `restOf` must cover the position, the receipt
  state without what `wsOf`/`trieOf` cover, the recorder state, and the `fin` output).
  Note that the working set is a chunk-level key set, so `wsOf` must be a function of `StV`
  alone (e.g. the overlay's touched keys plus whatever `restOf` pins).
* **`encRest_inj`**: the remainder's byte encoder is injective (M5b/M5d: encoders for `RS`,
  `Recording`, `MainOutD2`).
* **`trie_ok`**: `trieOf v` is fully revealed and well-formed. The spec's `Ovl.trie` is a partial
  trie (`revealTrie`); lane E takes its full expansion here and puts the reveal shape (a function
  of the chunk's witness) in `restOf`.
* **`ws_ok`**, **`ws_len`**, **`depth_lt`**, **`idx_lt`**: range facts (value lengths `< 2^24`,
  the list fits the tree, `depth < 64`, the change index `< 2^64`).
* `leafBlock` and **`leafBlock_inj`**: the 128-byte leaf block (`Ws.leafBlock`, field limbs as
  bytes) is injective on well-formed leaves (M5b: from `WsCost.leafLimb_inj`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StateM5a.StateView

open NearSpec NearSpecV3 NearSpecV3.D2 StateM5a.Walk StateM5a.SerInj
open NearSpecV3.E2E.Bnd (StV ViewImpl Coll Sha384Coll bdigest bdigest_length sha384 sha384_length
  digestLen)

/-! ## Collision events -/

/-- A SHA-256 collision. -/
def Sha256Coll : Prop := ∃ a b : Bytes, a ≠ b ∧ sha256 a = sha256 b

theorem sha256CR_of_not (h : ¬ Sha256Coll) : Sha256CR := by
  intro a b hab
  classical
  by_cases hne : a = b
  · exact hne
  · exact absurd ⟨a, b, hne, hab⟩ h

/-- A full SHA-384 collision is a `bdigest` collision. -/
theorem sha384_coll {a b : Bytes} (hne : a ≠ b) (h : sha384 a = sha384 b) : Sha384Coll :=
  ⟨a, b, hne, by simp only [bdigest, h]⟩

/-- The working-set leaf digest: the first 48 bytes of one SHA-512 compression of a block from
the SHA-384 initial value. -/
def cmp384 (b : List Nat) : Bytes :=
  (SHA512.digestBytes (SHA512.compress NearSpecV3.E2E.Bnd.IV384 b)).take 48

theorem cmp384_length (b : List Nat) : (cmp384 b).length = 48 := by
  simp [cmp384, SHA512.digestBytes_length _ (SHA512.compress_length _ _)]

/-- A collision of the leaf compression. -/
def LeafColl : Prop := ∃ b b' : List Nat, b ≠ b' ∧ cmp384 b = cmp384 b'

/-! ## The working-set tree -/

/-- An inner node: SHA-384 of `left48 ‖ right48`. -/
def nodeH (l r : Bytes) : Bytes := sha384 (l ++ r)

/-- The zero digest of an unused leaf. -/
def zero48 : Bytes := List.replicate 48 0

theorem root_some : ∀ (D : Nat) (l : List Bytes), l.length = 2 ^ D →
    ∃ x, Merkle.root nodeH D l = some x
  | 0, l, h => by
    match l, h with
    | [x], _ => exact ⟨x, rfl⟩
  | D + 1, l, h => by
    have : (Merkle.up nodeH l).length = 2 ^ D := by
      rw [Merkle.up_length, h, Nat.pow_succ]; omega
    exact root_some D _ this

theorem up_mem_length : ∀ (l : List Bytes), ∀ x ∈ Merkle.up nodeH l, x.length = 48
  | a :: b :: r, x, hx => by
    simp only [Merkle.up, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact sha384_length _
    · exact up_mem_length r x hx
  | [], x, hx => by simp [Merkle.up] at hx
  | [_], x, hx => by simp [Merkle.up] at hx

/-- One level: equal parents of two equal-length lists of 48-byte digests are equal children, or
a SHA-384 collision. -/
theorem up_binding : ∀ (l l' : List Bytes), l.length = l'.length → l.length % 2 = 0 →
    (∀ x ∈ l, x.length = 48) → (∀ x ∈ l', x.length = 48) →
    Merkle.up nodeH l = Merkle.up nodeH l' → l = l' ∨ Sha384Coll
  | [], [], _, _, _, _, _ => .inl rfl
  | a :: b :: r, c :: d :: r', hl, he, h1, h2, hu => by
    simp only [Merkle.up, List.cons.injEq] at hu
    obtain ⟨hn, hr⟩ := hu
    classical
    by_cases hab : a ++ b = c ++ d
    · obtain ⟨rfl, rfl⟩ := List.append_inj hab
        (by rw [h1 a (by simp), h2 c (by simp)])
      rcases up_binding r r' (by simp at hl; omega) (by simp at he; omega)
        (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx])) hr with h | h
      · exact .inl (by rw [h])
      · exact .inr h
    · exact .inr (sha384_coll hab hn)
  | [], _ :: _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _, _ => by simp at hl
  | [_], _, _, he, _, _, _ => by simp at he
  | _ :: _ :: _, [_], hl, _, _, _, _ => by simp at hl

/-- **Merkle root binding.** Two depth-`D` trees of 48-byte leaf digests with the same root have
the same leaves, or there is a SHA-384 collision. -/
theorem merkle_binding : ∀ (D : Nat) (l l' : List Bytes), l.length = 2 ^ D → l'.length = 2 ^ D →
    (∀ x ∈ l, x.length = 48) → (∀ x ∈ l', x.length = 48) →
    Merkle.root nodeH D l = Merkle.root nodeH D l' → l = l' ∨ Sha384Coll
  | 0, l, l', h1, h2, _, _, hr => by
    match l, l', h1, h2 with
    | [x], [y], _, _ =>
      simp only [Merkle.root, Option.some.injEq] at hr
      exact .inl (by rw [hr])
  | D + 1, l, l', h1, h2, w1, w2, hr => by
    have u1 : (Merkle.up nodeH l).length = 2 ^ D := by
      rw [Merkle.up_length, h1, Nat.pow_succ]; omega
    have u2 : (Merkle.up nodeH l').length = 2 ^ D := by
      rw [Merkle.up_length, h2, Nat.pow_succ]; omega
    rcases merkle_binding D _ _ u1 u2 (up_mem_length l) (up_mem_length l') hr with h | h
    · exact up_binding l l' (by rw [h1, h2]) (by rw [h1, Nat.pow_succ]; omega) w1 w2 h
    · exact .inr h

/-! ## Working-set entries and leaves -/

/-- A plain working-set entry: key, pre-value, current value (`none` = absent), written flag. -/
abbrev Entry := Bytes × Option Bytes × Option Bytes × Bool

/-- A circuit value ref: present flag, length, value hash. -/
structure VRef where
  present : Bool
  len : Nat
  h : Bytes
  deriving DecidableEq

/-- A circuit leaf: key hash, pre and current value refs, written flag. -/
structure WsLeaf where
  kd : Bytes
  pre : VRef
  cur : VRef
  wr : Bool
  deriving DecidableEq

def VRef.WF (r : VRef) : Prop := r.h.length = 32 ∧ r.len < 2 ^ 24
def WsLeaf.WF (l : WsLeaf) : Prop := l.kd.length = 32 ∧ l.pre.WF ∧ l.cur.WF

def vref : Option Bytes → VRef
  | none => ⟨false, 0, List.replicate 32 0⟩
  | some x => ⟨true, x.length, sha256 x⟩

def leafOf (e : Entry) : WsLeaf := ⟨sha256 e.1, vref e.2.1, vref e.2.2.1, e.2.2.2⟩

/-- Value lengths fit the leaf's 24-bit length fields. -/
def OptOk (v : Option Bytes) : Prop := ∀ x, v = some x → x.length < 2 ^ 24
def Entry.Ok (e : Entry) : Prop := OptOk e.2.1 ∧ OptOk e.2.2.1

theorem vref_wf (v : Option Bytes) (h : OptOk v) : (vref v).WF := by
  cases v with
  | none => simp [vref, VRef.WF]
  | some x => exact ⟨ArenaCore.sha256_length x, h x rfl⟩

theorem leafOf_wf (e : Entry) (h : e.Ok) : (leafOf e).WF :=
  ⟨ArenaCore.sha256_length _, vref_wf _ h.1, vref_wf _ h.2⟩

theorem sha_eq_or (a b : Bytes) (h : sha256 a = sha256 b) : a = b ∨ Sha256Coll := by
  classical
  by_cases hab : a = b
  · exact .inl hab
  · exact .inr ⟨a, b, hab, h⟩

theorem vref_inj (a b : Option Bytes) (h : vref a = vref b) : a = b ∨ Sha256Coll := by
  cases a <;> cases b <;> simp only [vref, VRef.mk.injEq] at h
  · exact .inl rfl
  · simp at h
  · simp at h
  · rename_i x y
    rcases sha_eq_or x y h.2.2 with h | h
    · exact .inl (by rw [h])
    · exact .inr h

/-- **The leaf map is injective** modulo SHA-256 collisions. -/
theorem leafOf_inj (e e' : Entry) (h : leafOf e = leafOf e') : e = e' ∨ Sha256Coll := by
  obtain ⟨k, p, c, w⟩ := e
  obtain ⟨k', p', c', w'⟩ := e'
  simp only [leafOf, WsLeaf.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases sha_eq_or _ _ h1 with h1 | h1
  · rcases vref_inj _ _ h2 with h2 | h2
    · rcases vref_inj _ _ h3 with h3 | h3
      · exact .inl (by subst h1; subst h2; subst h3; subst h4; rfl)
      · exact .inr h3
    · exact .inr h2
  · exact .inr h1

/-! ## The trie root -/

mutual
/-- Fully revealed: no hash stub, every value slot revealed. -/
def Rev : PTrie → Prop
  | .hash _ => False
  | .leaf _ s _ => ∃ x, s = .val x
  | .ext _ c _ => Rev c
  | .branch v cs _ => (∀ s, v = some s → ∃ x, s = .val x) ∧ KRev cs
def KRev : Kids → Prop
  | .nil => True
  | .none r => KRev r
  | .some c r => Rev c ∧ KRev r
end

/-- A slot as its `ValueRef`. -/
def sref : Slot → Slot
  | .val v => .ref v.length (sha256 v)
  | .ref l h => .ref l h

/-- Children as hash stubs. -/
def stubK : Kids → Kids
  | .nil => .nil
  | .none r => .none (stubK r)
  | .some c r => .some (.hash c.hashOf) (stubK r)

/-- A node one level deep: children stubs, value slots as refs (a row's node). -/
def shal : PTrie → PTrie
  | .hash h => .hash h
  | .leaf k v m => .leaf k (sref v) m
  | .ext k c m => .ext k (.hash c.hashOf) m
  | .branch v cs m => .branch (v.map sref) (stubK cs) m

theorem sref_valueRef (s : Slot) : (sref s).valueRef = s.valueRef := by cases s <;> rfl

theorem sref_ok (s : Slot) (h : slotOk s = true) : slotOk (sref s) = true := by
  cases s <;> simp_all [sref, slotOk, ArenaCore.sha256_length]

theorem stubK_hashes : ∀ cs : Kids, Kids.hashes (stubK cs) = Kids.hashes cs
  | .nil => rfl
  | .none r => by simp only [stubK, Kids.hashes]; exact stubK_hashes r
  | .some c r => by simp only [stubK, Kids.hashes, PTrie.hashOf]; rw [stubK_hashes r]

theorem stubK_bitmap : ∀ (cs : Kids) (i : Nat), kidsBitmap (stubK cs) i = kidsBitmap cs i
  | .nil, _ => rfl
  | .none r, i => by simp only [stubK, kidsBitmap]; exact stubK_bitmap r _
  | .some c r, i => by simp only [stubK, kidsBitmap]; rw [stubK_bitmap r]

theorem stubK_wf : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → Kids.wf (stubK cs) n = true
  | .nil, _, h => h
  | .none r, n, h => by
    simp only [stubK, Kids.wf, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, stubK_wf r _ h.2⟩
  | .some c r, n, h => by
    simp only [stubK, Kids.wf, Bool.and_eq_true] at h ⊢
    refine ⟨⟨h.1.1, ?_⟩, stubK_wf r _ h.2⟩
    simp only [PTrie.wf, beq_iff_eq]
    exact hashOf_length c h.1.2

theorem stubK_at : ∀ (cs : Kids) (n : Nat) (c : PTrie), Kids.at (stubK cs) n = some c →
    ∃ h, c = .hash h
  | .nil, _, _, h => by simp [stubK, Kids.at] at h
  | .none r, 0, _, h => by simp [stubK, Kids.at] at h
  | .none r, n + 1, c, h => by simp only [stubK, Kids.at] at h; exact stubK_at r n c h
  | .some c' r, 0, c, h => by
    simp only [stubK, Kids.at, Option.some.injEq] at h
    exact ⟨_, h.symm⟩
  | .some c' r, n + 1, c, h => by simp only [stubK, Kids.at] at h; exact stubK_at r n c h

theorem hashOf_shal (t : PTrie) : (shal t).hashOf = t.hashOf := by
  cases t with
  | hash h => rfl
  | leaf k v m => simp only [shal, PTrie.hashOf, sref_valueRef]
  | ext k c m => simp only [shal, PTrie.hashOf]
  | branch v cs m =>
    cases v <;> simp only [shal, Option.map, PTrie.hashOf, sref_valueRef, stubK_hashes, stubK_bitmap]

theorem wf_shal (t : PTrie) (h : t.wf = true) : (shal t).wf = true := by
  cases t with
  | hash h => exact h
  | leaf k v m =>
    simp only [shal, PTrie.wf, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨h.1.1.1, sref_ok v h.1.1.2⟩, h.1.2⟩, h.2⟩
  | ext k c m =>
    simp only [shal, PTrie.wf, Bool.and_eq_true, beq_iff_eq] at h ⊢
    exact ⟨⟨⟨h.1.1.1, hashOf_length c h.1.1.2⟩, h.1.2⟩, h.2⟩
  | branch v cs m =>
    cases v <;> simp only [shal, Option.map, PTrie.wf, Bool.and_eq_true] at h ⊢
    · exact ⟨⟨h.1.1, stubK_wf cs 16 h.1.2⟩, h.2⟩
    · exact ⟨⟨sref_ok _ h.1.1, stubK_wf cs 16 h.1.2⟩, h.2⟩

theorem shallow_shal (t : PTrie) : Shallow (shal t) := by
  cases t with
  | hash h => trivial
  | leaf k v m => cases v <;> exact ⟨_, _, rfl⟩
  | ext k c m => exact ⟨_, rfl⟩
  | branch v cs m =>
    refine ⟨fun s hs => ?_, stubK_at cs⟩
    cases v with
    | none => simp [Option.map] at hs
    | some s' =>
      simp only [Option.map, Option.some.injEq] at hs
      subst hs; cases s' <;> exact ⟨_, _, rfl⟩

theorem rev_ne_hash : ∀ t : PTrie, Rev t → ∀ h, t ≠ .hash h
  | .hash _, hr, _, _ => by simp [Rev] at hr
  | .leaf .., _, _, he => by cases he
  | .ext .., _, _, he => by cases he
  | .branch .., _, _, he => by cases he

theorem shal_ne_hash (t : PTrie) (hr : Rev t) : ∀ h, shal t ≠ .hash h := by
  intro h he
  cases t with
  | hash _ => simp [Rev] at hr
  | leaf => cases he
  | ext => cases he
  | branch => cases he

theorem slot_eq (hCR : Sha256CR) {x y : Bytes} (h : SlotRefines (sref (.val x)) (.val y)) : x = y := by
  rcases h with h | ⟨w, h1, h2⟩
  · cases h
  · simp only [sref, Slot.ref.injEq] at h1
    simp only [Slot.val.injEq] at h2
    subst h2
    exact hCR _ _ h1.2

mutual
/-- **Fully revealed tries are determined by their hash** (under `Sha256CR`). -/
theorem rev_eq (hCR : Sha256CR) : ∀ t t' : PTrie, Rev t → Rev t' → t.wf = true → t'.wf = true →
    t.hashOf = t'.hashOf → t = t'
  | t, t', r, r', w, w', hh => by
    have hr := refinedBy_of_hash' hCR (wf_shal t w) w' (shal_ne_hash t r) (rev_ne_hash t' r')
      (shallow_shal t) (by rw [hashOf_shal]; exact hh)
    match t, t', r, r', w, w', hr with
    | .leaf k s m, .leaf k' s' m', r, r', _, _, hr =>
      simp only [shal, PTrie.refinedBy] at hr
      obtain ⟨x, rfl⟩ := r
      obtain ⟨y, rfl⟩ := r'
      obtain ⟨rfl, rfl, hs⟩ := hr
      rw [slot_eq hCR hs]
    | .ext k c m, .ext k' c' m', r, r', w, w', hr =>
      simp only [shal, PTrie.refinedBy] at hr
      obtain ⟨rfl, rfl, hc⟩ := hr
      simp only [PTrie.wf, Bool.and_eq_true] at w w'
      simp only [Rev] at r r'
      rw [rev_eq hCR c c' r r' w.1.1.2 w'.1.1.2 hc]
    | .branch v cs m, .branch v' cs' m', r, r', w, w', hr =>
      simp only [shal, PTrie.refinedBy] at hr
      obtain ⟨rfl, hv, hk⟩ := hr
      simp only [PTrie.wf, Bool.and_eq_true] at w w'
      simp only [Rev] at r r'
      have hcs := krev_eq hCR cs cs' 16 16 r.2 r'.2 w.1.2 w'.1.2 hk
      subst hcs
      have : v = v' := by
        cases v with
        | none => cases v' with
          | none => rfl
          | some => simp [Option.map, OptSlotRefines] at hv
        | some s => cases v' with
          | none => simp [Option.map, OptSlotRefines] at hv
          | some s' =>
            obtain ⟨x, rfl⟩ := r.1 s rfl
            obtain ⟨y, rfl⟩ := r'.1 s' rfl
            simp only [Option.map, OptSlotRefines] at hv
            rw [slot_eq hCR hv]
      rw [this]
    | .leaf .., .ext .., _, _, _, _, hr => simp [shal, PTrie.refinedBy] at hr
    | .leaf .., .branch .., _, _, _, _, hr => simp [shal, PTrie.refinedBy] at hr
    | .ext .., .leaf .., _, _, _, _, hr => simp [shal, PTrie.refinedBy] at hr
    | .ext .., .branch .., _, _, _, _, hr => simp [shal, PTrie.refinedBy] at hr
    | .branch .., .leaf .., _, _, _, _, hr => simp [shal, PTrie.refinedBy] at hr
    | .branch .., .ext .., _, _, _, _, hr => simp [shal, PTrie.refinedBy] at hr
    | .hash _, _, r, _, _, _, _ => simp [Rev] at r
    | .leaf .., .hash _, _, r', _, _, _ => simp [Rev] at r'
    | .ext .., .hash _, _, r', _, _, _ => simp [Rev] at r'
    | .branch .., .hash _, _, r', _, _, _ => simp [Rev] at r'
theorem krev_eq (hCR : Sha256CR) : ∀ (cs cs' : Kids) (n n' : Nat), KRev cs → KRev cs' →
    Kids.wf cs n = true → Kids.wf cs' n' = true → Kids.refinedBy (stubK cs) cs' → cs = cs'
  | .nil, .nil, _, _, _, _, _, _, _ => rfl
  | .none r, .none r', n, n', k, k', w, w', h => by
    simp only [stubK, Kids.refinedBy] at h
    simp only [KRev] at k k'
    simp only [Kids.wf, Bool.and_eq_true] at w w'
    rw [krev_eq hCR r r' _ _ k k' w.2 w'.2 h]
  | .some c r, .some c' r', n, n', k, k', w, w', h => by
    simp only [stubK, Kids.refinedBy, PTrie.refinedBy] at h
    simp only [KRev] at k k'
    simp only [Kids.wf, Bool.and_eq_true] at w w'
    rw [rev_eq hCR c c' k.1 k'.1 w.1.2 w'.1.2 h.1, krev_eq hCR r r' _ _ k.2 k'.2 w.2 w'.2 h.2]
  | .nil, .none _, _, _, _, _, _, _, h => by simp [stubK, Kids.refinedBy] at h
  | .nil, .some .., _, _, _, _, _, _, h => by simp [stubK, Kids.refinedBy] at h
  | .none _, .nil, _, _, _, _, _, _, h => by simp [stubK, Kids.refinedBy] at h
  | .none _, .some .., _, _, _, _, _, _, h => by simp [stubK, Kids.refinedBy] at h
  | .some .., .nil, _, _, _, _, _, _, h => by simp [stubK, Kids.refinedBy] at h
  | .some .., .none _, _, _, _, _, _, _, h => by simp [stubK, Kids.refinedBy] at h
end

/-- **Trie root binding.** Two fully revealed, well-formed tries with the same root hash are equal,
or there is a SHA-256 collision. -/
theorem trie_binding (t t' : PTrie) (r : Rev t) (r' : Rev t') (w : t.wf = true) (w' : t'.wf = true)
    (h : t.hashOf = t'.hashOf) : t = t' ∨ Sha256Coll := by
  classical
  by_cases hc : Sha256Coll
  · exact .inr hc
  · exact .inl (rev_eq (sha256CR_of_not hc) t t' r r' w w' h)

/-! ## The commitment record and its serialization -/

/-- **The state commitment.** -/
structure StCommit where
  tag : Nat
  ws : Bytes
  wsLen : Nat
  trie : Bytes
  idx : Nat
  rest : Bytes

def StCommit.WF (c : StCommit) : Prop :=
  c.tag < 256 ∧ c.ws.length = 48 ∧ c.wsLen < 2 ^ 64 ∧ c.trie.length = 32 ∧ c.idx < 2 ^ 64 ∧
    c.rest.length = digestLen

/-- `[tag] ‖ ws ‖ u64 wsLen ‖ trie ‖ u64 idx ‖ rest`. -/
def StCommit.ser (c : StCommit) : Bytes :=
  [UInt8.ofNat c.tag] ++ c.ws ++ u64 c.wsLen ++ c.trie ++ u64 c.idx ++ c.rest

/-- **The serialization is injective** on well-formed records. -/
theorem ser_inj (c d : StCommit) (hc : c.WF) (hd : d.WF) (h : c.ser = d.ser) : c = d := by
  obtain ⟨tg, ws, n, tr, i, r⟩ := c
  obtain ⟨tg', ws', n', tr', i', r'⟩ := d
  simp only [StCommit.WF] at hc hd
  obtain ⟨t1, w1, n1, r1, i1, s1⟩ := hc
  obtain ⟨t2, w2, n2, r2, i2, s2⟩ := hd
  simp only [StCommit.ser] at h
  obtain ⟨h, hs⟩ := List.append_inj' h (by rw [s1, s2])
  obtain ⟨h, hi⟩ := List.append_inj' h (by simp [u64, leN_len])
  obtain ⟨h, hr⟩ := List.append_inj' h (by rw [r1, r2])
  obtain ⟨h, hn⟩ := List.append_inj' h (by simp [u64, leN_len])
  obtain ⟨h, hw⟩ := List.append_inj' h (by rw [w1, w2])
  simp only [List.cons.injEq, and_true] at h
  have ht := congrArg UInt8.toNat h
  rw [ofNat_toNat, ofNat_toNat] at ht
  have hi' := leN_inj 8 _ _ hi (by simpa using i1) (by simpa using i2)
  have hn' := leN_inj 8 _ _ hn (by simpa using n1) (by simpa using n2)
  simp only [StCommit.mk.injEq]
  exact ⟨by omega, hw, hn', hr, hi', hs⟩

/-! ## The parameters and the commitment -/

/-- The constructor of a state component. -/
def tagOf : StV → Nat
  | .none => 0
  | .eng .. => 1
  | .fin .. => 2

/-- **The parameters of the state view**: the projection of `StV` onto the state lane's parts and
the remainder, with the obligations later milestones discharge. -/
structure StViewParams where
  /-- working-set tree depth -/
  depth : Nat
  depth_lt : depth < 64
  /-- the working set (key-sorted entries) -/
  wsOf : StV → List Entry
  ws_len : ∀ v, (wsOf v).length ≤ 2 ^ depth
  ws_ok : ∀ v, ∀ e ∈ wsOf v, e.Ok
  /-- the (fully revealed) trie whose root `TCH` carries -/
  trieOf : StV → PTrie
  trie_ok : ∀ v, Rev (trieOf v) ∧ (trieOf v).wf = true
  /-- the change index -/
  idxOf : StV → Nat
  idx_lt : ∀ v, idxOf v < 2 ^ 64
  /-- the remainder -/
  Rest : Type
  restOf : StV → Rest
  encRest : Rest → Bytes
  encRest_inj : ∀ a b, encRest a = encRest b → a = b
  /-- the 128-byte leaf block (`Ws.leafBlock`) -/
  leafBlock : WsLeaf → List Nat
  leafBlock_inj : ∀ a b, a.WF → b.WF → leafBlock a = leafBlock b → a = b
  /-- the parts determine the component -/
  proj_inj : ∀ a b, tagOf a = tagOf b → wsOf a = wsOf b → trieOf a = trieOf b →
    idxOf a = idxOf b → restOf a = restOf b → a = b

variable (P : StViewParams)

/-- A working-set leaf digest. -/
def leafD (e : Entry) : Bytes := cmp384 (P.leafBlock (leafOf e))

/-- The `2^depth` leaf digests (zero-padded). -/
def wsLeaves (es : List Entry) : List Bytes :=
  es.map (leafD P) ++ List.replicate (2 ^ P.depth - es.length) zero48

/-- The working-set root (`RCH`). -/
def wsRoot (es : List Entry) : Bytes := (Merkle.root nodeH P.depth (wsLeaves P es)).getD []

/-- The commitment of a state component. -/
def commitOf (v : StV) : StCommit where
  tag := tagOf v
  ws := wsRoot P (P.wsOf v)
  wsLen := (P.wsOf v).length
  trie := (P.trieOf v).hashOf
  idx := P.idxOf v
  rest := bdigest (P.encRest (P.restOf v))

/-- **The state commitment** (`ViewImpl.stD`). -/
def stD (v : StV) : Bytes := bdigest (commitOf P v).ser

theorem wsLeaves_length (es : List Entry) (h : es.length ≤ 2 ^ P.depth) :
    (wsLeaves P es).length = 2 ^ P.depth := by
  simp only [wsLeaves, List.length_append, List.length_map, List.length_replicate]; omega

theorem wsLeaves_mem (es : List Entry) : ∀ x ∈ wsLeaves P es, x.length = 48 := by
  intro x hx
  simp only [wsLeaves, List.mem_append, List.mem_map, List.mem_replicate] at hx
  rcases hx with ⟨e, -, rfl⟩ | ⟨-, rfl⟩
  · exact cmp384_length _
  · rfl

theorem root_mem : ∀ (D : Nat) (l : List Bytes) (x : Bytes), (∀ y ∈ l, y.length = 48) →
    Merkle.root nodeH D l = some x → x.length = 48
  | 0, l, x, hl, hr => by
    match l, hr with
    | [y], hr =>
      simp only [Merkle.root, Option.some.injEq] at hr
      subst hr; exact hl _ (by simp)
  | D + 1, l, x, _, hr => root_mem D _ x (up_mem_length l) hr

theorem wsRoot_length (es : List Entry) (h : es.length ≤ 2 ^ P.depth) :
    (wsRoot P es).length = 48 := by
  obtain ⟨x, hx⟩ := root_some P.depth _ (wsLeaves_length P es h)
  simp only [wsRoot, hx, Option.getD_some]
  exact root_mem _ _ x (wsLeaves_mem P es) hx

theorem commitOf_wf (v : StV) : (commitOf P v).WF := by
  have hd : 2 ^ P.depth < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) P.depth_lt
  refine ⟨by cases v <;> simp [commitOf, tagOf], wsRoot_length P _ (P.ws_len v), ?_,
    hashOf_length _ (P.trie_ok v).2, P.idx_lt v, bdigest_length _⟩
  have := P.ws_len v
  simp only [commitOf]; omega

/-- Equal leaf-digest lists of well-formed entries: equal entries, or a collision. -/
theorem leaves_binding : ∀ (es es' : List Entry), (∀ e ∈ es, e.Ok) → (∀ e ∈ es', e.Ok) →
    es.map (leafD P) = es'.map (leafD P) → es = es' ∨ Sha256Coll ∨ LeafColl
  | [], [], _, _, _ => .inl rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | e :: es, e' :: es', ho, ho', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    classical
    by_cases hb : P.leafBlock (leafOf e) = P.leafBlock (leafOf e')
    · have hl := P.leafBlock_inj _ _ (leafOf_wf e (ho e (by simp)))
        (leafOf_wf e' (ho' e' (by simp))) hb
      rcases leafOf_inj e e' hl with rfl | hc
      · rcases leaves_binding es es' (fun x hx => ho x (by simp [hx]))
          (fun x hx => ho' x (by simp [hx])) h2 with h | h
        · exact .inl (by rw [h])
        · exact .inr h
      · exact .inr (.inl hc)
    · exact .inr (.inr ⟨_, _, hb, h1⟩)

/-- **Working-set root binding.** Equal roots and entry counts give equal working sets, or a
collision. -/
theorem wsRoot_binding (es es' : List Entry) (l1 : es.length ≤ 2 ^ P.depth)
    (l2 : es'.length ≤ 2 ^ P.depth) (o1 : ∀ e ∈ es, e.Ok) (o2 : ∀ e ∈ es', e.Ok)
    (hn : es.length = es'.length) (h : wsRoot P es = wsRoot P es') :
    es = es' ∨ Sha384Coll ∨ Sha256Coll ∨ LeafColl := by
  obtain ⟨x, hx⟩ := root_some P.depth _ (wsLeaves_length P es l1)
  obtain ⟨y, hy⟩ := root_some P.depth _ (wsLeaves_length P es' l2)
  simp only [wsRoot, hx, hy, Option.getD_some] at h
  subst h
  rcases merkle_binding P.depth _ _ (wsLeaves_length P es l1) (wsLeaves_length P es' l2)
    (wsLeaves_mem P es) (wsLeaves_mem P es') (by rw [hx, hy]) with h | h
  · simp only [wsLeaves] at h
    obtain ⟨h, -⟩ := List.append_inj h (by simp [hn])
    rcases leaves_binding P es es' o1 o2 h with h | h | h
    · exact .inl h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  · exact .inr (.inl h)

/-- **The binding lemma.** A collision of the state commitment is a SHA-384 (42-byte) collision,
a SHA-256 collision, or a leaf-compression collision. -/
theorem stD_binding (h : Coll (stD P)) : Sha384Coll ∨ Sha256Coll ∨ LeafColl := by
  obtain ⟨a, b, hne, he⟩ := h
  classical
  by_cases hs : (commitOf P a).ser = (commitOf P b).ser
  · have hc := ser_inj _ _ (commitOf_wf P a) (commitOf_wf P b) hs
    have e1 : tagOf a = tagOf b := congrArg StCommit.tag hc
    have e2 : wsRoot P (P.wsOf a) = wsRoot P (P.wsOf b) := congrArg StCommit.ws hc
    have e3 : (P.wsOf a).length = (P.wsOf b).length := congrArg StCommit.wsLen hc
    have e4 : (P.trieOf a).hashOf = (P.trieOf b).hashOf := congrArg StCommit.trie hc
    have e5 : P.idxOf a = P.idxOf b := congrArg StCommit.idx hc
    have e6 : bdigest (P.encRest (P.restOf a)) = bdigest (P.encRest (P.restOf b)) :=
      congrArg StCommit.rest hc
    by_cases hr : P.encRest (P.restOf a) = P.encRest (P.restOf b)
    · have hr := P.encRest_inj _ _ hr
      rcases trie_binding _ _ (P.trie_ok a).1 (P.trie_ok b).1 (P.trie_ok a).2 (P.trie_ok b).2 e4
        with ht | ht
      · rcases wsRoot_binding P _ _ (P.ws_len a) (P.ws_len b) (P.ws_ok a) (P.ws_ok b) e3 e2
          with hw | hw
        · exact absurd (P.proj_inj a b e1 hw ht e5 hr) hne
        · exact hw
      · exact .inr (.inl ht)
    · exact .inl ⟨_, _, hr, e6⟩
  · exact .inl ⟨_, _, hs, he⟩

/-- `stD_binding` into a caller's `Bad`. -/
theorem stD_binding_bad (Bad : Prop) (hsha : Sha384Coll → Bad) (h256 : Sha256Coll → Bad)
    (hleaf : LeafColl → Bad) (h : Coll (stD P)) : Bad := by
  rcases stD_binding P h with h | h | h
  · exact hsha h
  · exact h256 h
  · exact hleaf h

/-- **The `hst` premise of `viewImpl_binding_bad`** for any view whose state component is this
instance. -/
theorem viewImpl_hst (V : ViewImpl) (hV : V.stD = stD P) (Bad : Prop) (hsha : Sha384Coll → Bad)
    (h256 : Sha256Coll → Bad) (hleaf : LeafColl → Bad) : Coll V.stD → Bad := by
  rw [hV]; exact stD_binding_bad P Bad hsha h256 hleaf

/-- `viewImpl_binding_bad` with this state component plugged in. -/
theorem viewImpl_binding_st (V : ViewImpl) (hV : V.stD = stD P) (Bad : Prop)
    (hwf : ∀ x, (V.bnd x).WF) (hsha : Sha384Coll → Bad) (h256 : Sha256Coll → Bad)
    (hleaf : LeafColl → Bad) (hctx : Coll V.ctxD → Bad) (hout : Coll V.outD → Bad)
    (hvm : Coll V.vmD → Bad) (hwasm : Coll V.wasmD → Bad)
    (h : NearSpecV3.E2E.Bnd.BndCollision V.bnd) : Bad :=
  NearSpecV3.E2E.Bnd.viewImpl_binding_bad V Bad hwf hsha hctx
    (viewImpl_hst P V hV Bad hsha h256 hleaf) hout hvm hwasm h

end StateM5a.StateView
