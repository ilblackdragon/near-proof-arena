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

## Status

**Done and proved** (`[propext, Classical.choice, Quot.sound]`, no `sorry`):
* `Gas.encode`, `Gas.wf`, `Gas.decode`
* `encArray_u32` — `readU32` peels the element count, no remainder
* `encArray_u32_append` — same, carrying the remainder (what the round trip needs)
* `readWords_concatAll_append` — `n` words re-assemble, with a trailing remainder

**NOT proved:** `Gas.decode_encode_statement` is stated with a `sorry`. It is deliberately not
named `Gas.decode_encode` so it cannot be mistaken for an established round trip, and this
module is **not imported by `NearSpecV3.lean`**, so the `sorry` cannot leak into the library
or any gate (`lake build NearSpecV3` still succeeds at 65 jobs).

All the rewrites fire; the residue is a nested `match` on `readWords` that `simp only` does
not eliminate — it rewrites inside the arms instead. Closing it needs a `cases` split on the
`readWords` result or restructuring the statement, which is design work rather than tactics.

## The useful design finding

`encArray` uses a 4-byte **element count**, not a byte length. The count is what `Gas.decode`
needs to know how many words to read, and `C.nKeys = 11` bounds it. My first version used
`borshBytes` (byte length) and the decode lemma would not close — that is how the distinction
surfaced. `Gas.wf` therefore also requires `special.size < 2^32`.
-/

namespace NearSpecV3.Wasm

open NearSpec

/-- `encArray`: 4-byte **element count**, then each element's encoding. The count (not the
byte length) is what `Gas.decode` reads, and `C.nKeys = 11` bounds it, so a `u32` is ample.
Decoding is therefore `readU32` for the count, then that many `leN 8` reads. -/
def encArray {α} (f : α → Bytes) (xs : Array α) : Bytes :=
  NearSpec.u32 xs.size ++ NearSpec.concatAll (xs.toList.map f)

/-- Tag-free flat encoding: eleven scalar payloads, then the length-prefixed `special`. -/
def Gas.encode (gs : Gas) : Bytes :=
  leN 8 gs.burnt ++ leN 8 gs.promises ++ leN 8 gs.prepaid ++ leN 8 gs.limit ++
  leN 8 gs.g ++ leN 8 gs.host ++ leN 8 gs.action ++
  encArray (leN 8) gs.special ++
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
    NearSpec.readU32 (encArray f xs) =
      some (xs.size, NearSpec.concatAll (xs.toList.map f)) := by
  have hle : xs.size < 256^4 := by
    have : (256 : Nat)^4 = 2^32 := by decide
    rw [this]; exact h
  have hdef : encArray f xs =
      NearSpec.u32 xs.size ++ NearSpec.concatAll (xs.toList.map f) := rfl
  rw [hdef]
  have hu : NearSpec.u32 xs.size = NearSpec.leN 4 xs.size := rfl
  rw [hu]
  exact NearSpec.readLE_append 4 xs.size _ hle

/-- As `encArray_u32` but carrying a remainder, which is what the round trip needs. -/
theorem encArray_u32_append (f : Nat → NearSpec.Bytes) (xs : Array Nat) (rest : NearSpec.Bytes)
    (h : xs.size < 2^32) :
    NearSpec.readU32 (encArray f xs ++ rest) =
      some (xs.size, NearSpec.concatAll (xs.toList.map f) ++ rest) := by
  have hle : xs.size < 256^4 := by
    have : (256 : Nat)^4 = 2^32 := by decide
    rw [this]; exact h
  have hdef : encArray f xs ++ rest =
      NearSpec.u32 xs.size ++ (NearSpec.concatAll (xs.toList.map f) ++ rest) := by
    simp [encArray, NearSpec.u32, List.append_assoc]
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

/-- The round trip. **NOT PROVED** — see the file header.

The nine scalar `readLE_append` rewrites and the `encArray_u32_append` /
`readWords_concatAll_append` pair all fire, but the residual goal is a nested `match` on
`readWords` that `simp only` does not reduce: the rewrites rewrite *inside* the match arms
rather than eliminating the `match` itself. Closing it needs either a `cases` split on the
`readWords` result or the round trip restated as an equality of the assembled record, which
is a structural change rather than a tactic tweak. Left as a documented gap.
-/
theorem Gas.decode_encode_statement (gs : Gas) (h : gs.wf) :
    Gas.decode (Gas.encode gs) = some gs := by
  sorry

end NearSpecV3.Wasm
