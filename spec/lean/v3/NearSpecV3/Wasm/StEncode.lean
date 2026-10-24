import NearSpecV3.Wasm.Segment

/-!
# A byte encoding of the machine state `St` (recursion track)

`Segment.lean` proves the segment fold over the *whole* machine state `St`, while the
aggregation layer needs each boundary state as a fixed-width vector of field elements
(`RangeStmt.s_a` / `s_e`). This file supplies the missing bridge: an injective,
length-prefixed byte encoding

```
St.encode : St → ByteArray
```

with `St.encode_injective : encode s = encode t → s = t`.

The encoding is **length-prefixed and tag-dispatching** so that no two distinct states share
a byte string. Every `Nat` is emitted as 8 little-endian bytes
(`u64`), every array/option carries its length or presence tag first. The one wrinkle is
that `Nat` is unbounded in Lean while `u64` is not, so `encode` is parameterised by a bound
`B` on every `Nat` it meets; `encodeInjective` is then stated for states bounded by `B`.
That bound is not a restriction in practice — the interpreter's counters (`pc`, `g`, gas,
`dataCount`, receipt indices) are all bounded far below `2^64` — but it must be **stated**
rather than assumed, which is why it appears in the theorem.

This is deliberately not a hash: injectivity is what the fold-commutation theorem needs, and
a hash would only give collision resistance. The commitment layer
(`hash_range`, in `nv/agg.rs`) hashes *this* byte string with SHA-384 at the aggregate level.

**Status (2026-10-23).** Only the *primitives* are done and this file compiles clean:
`encNat` (8-byte little-endian), `encList`, `encArray`, `encString`, `encOption`. They were
spot-checked by evaluation, which confirms the wire format:

```
encNat 258        = [2,1,0,0,0,0,0,0]        (little-endian, 8 bytes)
encNat 255 / 256  = [255,0,...] / [0,1,...]  (distinct, as required)
encString "ab"    = [2,0,0,0,0,0,0,0, 97,98] (length prefix then UTF-8)
encOption … none  = [0]                      (presence tag)
encList encNat [1,2] = [2,0,0,0,0,0,0,0, 1,0,…, 2,0,…]
```

**What is NOT done — and this is the honest part.** There is **no `St.encode`** yet and
**no injectivity theorem**. The type still needs dispatchers for `Val` (an inductive with
`i32/i64/f32/f64/ref`), `Gas`, `Frame`, `CallCtx`, `PRes`, `PromiseV`, `MAct`, `RealStore`,
and `St` itself — ten mutually-referencing encoders over structures containing
`Array ByteArray`, `List Frame`, `Array (ByteArray × ByteArray)` and `Option (ByteArray ×
Option ByteArray)`. Then each needs a round-trip lemma.

The proven way to get injectivity in this repo is **not** to reason about raw bit arithmetic
(which is where my first attempt stalled) but the `Claim.encode_injective` pattern in
`NearSpecV3/ClaimV3Props.lean:224`: write a strict **parser**, prove
`decode (encode x) = some x`, then derive `x₁ = x₂` by `Option.some.inj`. `NearSpecV3/Wire.lean`
already supplies `Parser`, `readU8/16/32/64` and `lift`, so the machinery exists — but
`Wire.lean` contains **no theorems**, so even the scalar round trips (`readU64 (u64 n) = n`
for `n < 2^64`) have to be proved first. That lemma is the true first step and it is not yet
written.

**Nothing here is wired to the PQ stack**, and no claim in this session depends on it
compiling. It is recorded as a correctly-scoped starting point rather than as progress
toward a finished leaf.
-/

namespace NearSpecV3.Wasm

/-- Little-endian `u64` encoding of a bounded `Nat`. -/
def encNat (n : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (fun i : Fin 8 => UInt8.ofNat (n >>> (8 * i.val))))

/-- Length prefix (as `encNat`) followed by the concatenated encodings.

**Not the same as `NearSpecV3.encList`** (`ClaimV3.lean:84`), which is the claim wire format
and uses a **4-byte** `u32` length. This one uses an **8-byte** length on purpose: a machine
state's arrays (`pages`, `actions`, `trie`) can in principle exceed `2^32` entries, and the
injectivity proof must not silently truncate a length. The two live in different namespaces
(`NearSpecV3.Wasm` vs `NearSpecV3`) so neither shadows the other. -/
def encList {α} (f : α → ByteArray) (xs : List α) : ByteArray :=
  encNat xs.length ++ ByteArray.mk (xs.toArray.flatMap (fun x => (f x).data))

/-- Same for `Array`. -/
def encArray {α} (f : α → ByteArray) (xs : Array α) : ByteArray :=
  encNat xs.size ++ ByteArray.mk (xs.flatMap (fun x => (f x).data))

/-- A `String` is encoded as its UTF-8 bytes with a length prefix. -/
def encString (s : String) : ByteArray :=
  encNat s.toUTF8.size ++ s.toUTF8

/-- `Option`: one presence byte, then the payload. -/
def encOption {α} (f : α → ByteArray) : Option α → ByteArray
  | none => ByteArray.mk #[0]
  | some x => ByteArray.mk #[1] ++ f x

end NearSpecV3.Wasm
