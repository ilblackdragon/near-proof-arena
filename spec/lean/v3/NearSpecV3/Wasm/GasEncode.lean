import NearSpec.ClaimCodec
import NearSpecV3.Wasm.Machine

/-!
# An injective byte encoding of `Gas`

`Gas` (`Machine.lean:113-125`) is the gas counter, and it is the second of the nine
structure encoders needed for the boundary-state serialiser (lane log §7.2).

```
structure Gas where
  burnt, promises, prepaid, limit, g : Nat
  host, action : Nat
  special : Array Nat        -- length C.nKeys = 11
  sendCompute : Nat
```

Every field is a `Nat`, so the encoding is a flat concatenation of `leN 8` payloads — the
fixed field count is what makes it order-determined, and no length prefix is needed for the
scalars. `special` is an `Array Nat` of *bounded* length (`C.nKeys = 11`, `Machine.lean:98`),
so it is length-prefixed (`encNat`-style 8-byte count) and each element is `leN 8`.

## The bound hypothesis

As with `Val`, the theorem takes `Gas.wf` — every `Nat` field below `2^64`. This is not an
extra assumption: `maxGasBurnt = 10^15` (`Machine.lean:29`), `prepaid` comes from a `u64`
attachment, and the `special` slots are per-cost gas values. The bound is a fact about the
machine made explicit at the interface, matching `Claim.encode_injective`'s `wf` hypothesis.

## Status: COMPLETE

All proved, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`:
* `Gas.encode`, `Gas.wf`, `Gas.decode`
* `encArray_u32`, `encArray_u32_append` — element-count prefix, with and without remainder
* `readWords_concatAll`, `readWords_concatAll_append` — re-assembling a word list
* **`Gas.decode_encode`** — the round trip
* **`Gas.encode_injective`** — follows by `Option.some.inj`

### The obstruction, and what fixed it

Two attempts stalled on the same thing: after the nine `readLE_append` rewrites fired, the
residual goal was a nested `match` on `readWords`, and `simp only` rewrites *inside* match
arms rather than eliminating the `match`.

The fix is one line of strategy: **establish the `readWords` result first**
(`hw : readWords ... = some (special.toList, leN 8 sendCompute)`), then `rw [hw]` after the
rewrites have fired. With the result already a `some (...)` value, the match reduces
definitionally and the record comparison closes. Same for the final `readLE` word.

This is why the earlier documentation called it "design work, not tactics" — and that was
right, but the design change turned out to be small. Generalising: for the remaining
encoders, prove the *inner readers* as standalone `... = some (...)` facts and rewrite them
in, rather than hoping `simp` will thread through a `match`.

## The useful design finding


`encArrayB` uses a 4-byte **element count**, not a byte length. The count is what `Gas.decode`
needs to know how many words to read, and `C.nKeys = 11` bounds it. My first version used
`borshBytes` (byte length) and the decode lemma would not close — that is how the distinction
surfaced. `Gas.wf` therefore also requires `special.size < 2^32`.
-/

namespace NearSpecV3.Wasm

open NearSpec

/-- `encArrayB`: 4-byte **element count**, then each element's encoding. The count (not the
byte length) is what `Gas.decode` reads, and `C.nKeys = 11` bounds it, so a `u32` is ample.
Decoding is therefore `readU32` for the count, then that many `leN 8` reads. -/
def encArrayB {α} (f : α → Bytes) (xs : Array α) : Bytes :=
  NearSpec.u32 xs.size ++ NearSpec.concatAll (xs.toList.map f)

/-- Tag-free flat encoding: eleven scalar payloads, then the length-prefixed `special`. -/
def Gas.encode (gs : Gas) : Bytes :=
  leN 8 gs.burnt ++ leN 8 gs.promises ++ leN 8 gs.prepaid ++ leN 8 gs.limit ++
  leN 8 gs.g ++ leN 8 gs.host ++ leN 8 gs.action ++
  encArrayB (leN 8) gs.special ++
  leN 8 gs.sendCompute

/-- Well-formed gas counter: every scalar fits in 64 bits, and each `special` slot does too. -/
def Gas.wf (gs : Gas) : Prop :=
  gs.burnt < 2^64 ∧ gs.promises < 2^64 ∧ gs.prepaid < 2^64 ∧ gs.limit < 2^64 ∧
  gs.g < 2^64 ∧ gs.host < 2^64 ∧ gs.action < 2^64 ∧ gs.sendCompute < 2^64 ∧
  (∀ x ∈ gs.special, x < 2^64) ∧ gs.special.size < 2^32

/-- Read `n` consecutive 8-byte little-endian words. -/
def readWords (n : Nat) (bs : Bytes) : Option (List Nat × Bytes) :=
  match n with
  | 0 => some ([], bs)
  | k + 1 =>
    match NearSpec.readLE 8 bs with
    | none => none
    | some (x, rest) =>
      match readWords k rest with
      | none => none
      | some (xs, r) => some (x :: xs, r)

/-- The decoder: fields in the same order `Gas.encode` writes them. -/
def Gas.decode (bs : Bytes) : Option Gas :=
  match NearSpec.readLE 8 bs with
  | none => none
  | some (burnt, r1) =>
  match NearSpec.readLE 8 r1 with
  | none => none
  | some (promises, r2) =>
  match NearSpec.readLE 8 r2 with
  | none => none
  | some (prepaid, r3) =>
  match NearSpec.readLE 8 r3 with
  | none => none
  | some (limit, r4) =>
  match NearSpec.readLE 8 r4 with
  | none => none
  | some (g, r5) =>
  match NearSpec.readLE 8 r5 with
  | none => none
  | some (host, r6) =>
  match NearSpec.readLE 8 r6 with
  | none => none
  | some (action, r7) =>
  match NearSpec.readU32 r7 with
  | none => none
  | some (nSpecial, r7b) =>
  match readWords nSpecial r7b with
  | none => none
  | some (specials, r9) =>
  match NearSpec.readLE 8 r9 with
  | none => none
  | some (sendCompute, _) =>
    some { burnt := burnt, promises := promises, prepaid := prepaid, limit := limit,
           g := g, host := host, action := action,
           special := specials.toArray, sendCompute := sendCompute }

/-- `u32` is `leN 4`, so `readU32` peels an element count. -/
theorem encArray_u32 (f : Nat → NearSpec.Bytes) (xs : Array Nat) (h : xs.size < 2^32) :
    NearSpec.readU32 (encArrayB f xs) =
      some (xs.size, NearSpec.concatAll (xs.toList.map f)) := by
  have hle : xs.size < 256^4 := by
    have : (256 : Nat)^4 = 2^32 := by decide
    rw [this]; exact h
  have hdef : encArrayB f xs =
      NearSpec.u32 xs.size ++ NearSpec.concatAll (xs.toList.map f) := rfl
  rw [hdef]
  have hu : NearSpec.u32 xs.size = NearSpec.leN 4 xs.size := rfl
  rw [hu]
  exact NearSpec.readLE_append 4 xs.size _ hle

/-- As `encArray_u32` but carrying a remainder, which is what the round trip needs. -/
theorem encArray_u32_append (f : Nat → NearSpec.Bytes) (xs : Array Nat) (rest : NearSpec.Bytes)
    (h : xs.size < 2^32) :
    NearSpec.readU32 (encArrayB f xs ++ rest) =
      some (xs.size, NearSpec.concatAll (xs.toList.map f) ++ rest) := by
  have hle : xs.size < 256^4 := by
    have : (256 : Nat)^4 = 2^32 := by decide
    rw [this]; exact h
  have hdef : encArrayB f xs ++ rest =
      NearSpec.u32 xs.size ++ (NearSpec.concatAll (xs.toList.map f) ++ rest) := by
    simp [encArrayB, NearSpec.u32, List.append_assoc]
  rw [hdef]
  have hu : NearSpec.u32 xs.size = NearSpec.leN 4 xs.size := rfl
  rw [hu]
  exact NearSpec.readLE_append 4 xs.size _ hle

/-- Reading back `n` words re-assembles the list, provided each fits in 64 bits. -/
theorem readWords_concatAll (xs : List Nat) (h : ∀ x ∈ xs, x < 2^64) :
    readWords xs.length (NearSpec.concatAll (xs.map (NearSpec.leN 8))) = some (xs, []) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hx : x < 2^64 := h x (by simp)
    have hr : ∀ y ∈ rest, y < 2^64 := fun y hy => h y (by simp [hy])
    have hle : x < 256^8 := by
      have : (256 : Nat)^8 = 2^64 := by decide
      rw [this]; exact hx
    simp only [List.length_cons, List.map_cons, NearSpec.concatAll, readWords]
    rw [NearSpec.readLE_append 8 x _ hle]
    simp only [ih hr]

/-- As `readWords_concatAll`, but with a trailing remainder (needed because `sendCompute`
follows `special` in the encoding). -/
theorem readWords_concatAll_append (xs : List Nat) (rest : NearSpec.Bytes)
    (h : ∀ x ∈ xs, x < 2^64) :
    readWords xs.length (NearSpec.concatAll (xs.map (NearSpec.leN 8)) ++ rest) =
      some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    have hx : x < 2^64 := h x (by simp)
    have hr : ∀ y ∈ tl, y < 2^64 := fun y hy => h y (by simp [hy])
    have hle : x < 256^8 := by
      have : (256 : Nat)^8 = 2^64 := by decide
      rw [this]; exact hx
    simp only [List.length_cons, List.map_cons, NearSpec.concatAll, readWords]
    rw [List.append_assoc]
    rw [NearSpec.readLE_append 8 x _ hle]
    simp only [ih hr]

/-- The round trip: decoding an encoded well-formed gas counter returns it unchanged.

The key step is `rw [hw]` — establishing the `readWords` result *before* unfolding, so the
rewriting happens on a `some (...)` value instead of getting stuck inside a `match` arm. -/
theorem Gas.decode_encode (gs : Gas) (h : gs.wf) : Gas.decode (Gas.encode gs) = some gs := by
  obtain ⟨hb, hp, hpr, hl, hg, hh, ha, hsc, hspec, hsize⟩ := h
  have hpow : (256:Nat)^8 = 2^64 := by decide
  have h8 : ∀ n, n < 2^64 → n < 256^8 := fun n hn => by rw [hpow]; exact hn
  have hs : ∀ x ∈ gs.special.toList, x < 2^64 := fun x hx =>
    hspec x (Array.mem_toList_iff.mp hx)
  -- establish the readWords result BEFORE unfolding, then rewrite it inside the match
  have hw : readWords gs.special.size
      (NearSpec.concatAll (gs.special.toList.map (NearSpec.leN 8)) ++ NearSpec.leN 8 gs.sendCompute)
      = some (gs.special.toList, NearSpec.leN 8 gs.sendCompute) := by
    have := readWords_concatAll_append gs.special.toList (NearSpec.leN 8 gs.sendCompute) hs
    simpa [Array.length_toList] using this
  simp only [Gas.encode, Gas.decode, List.append_assoc,
    NearSpec.readLE_append 8 gs.burnt _ (h8 _ hb),
    NearSpec.readLE_append 8 gs.promises _ (h8 _ hp),
    NearSpec.readLE_append 8 gs.prepaid _ (h8 _ hpr),
    NearSpec.readLE_append 8 gs.limit _ (h8 _ hl),
    NearSpec.readLE_append 8 gs.g _ (h8 _ hg),
    NearSpec.readLE_append 8 gs.host _ (h8 _ hh),
    NearSpec.readLE_append 8 gs.action _ (h8 _ ha),
    encArray_u32_append (NearSpec.leN 8) gs.special _ hsize]
  rw [hw]
  simp only [Array.toArray_toList]
  have hs8 : NearSpec.readLE 8 (NearSpec.leN 8 gs.sendCompute) = some (gs.sendCompute, []) := by
    have := NearSpec.readLE_append 8 gs.sendCompute [] (h8 _ hsc)
    simpa using this
  rw [hs8]

/-- `Gas` encodings are injective on well-formed values: decode is a left inverse. -/
theorem Gas.encode_injective {a b : Gas} (ha : a.wf) (hb : b.wf)
    (h : a.encode = b.encode) : a = b := by
  have h1 := Gas.decode_encode a ha
  have h2 := Gas.decode_encode b hb
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

end NearSpecV3.Wasm
