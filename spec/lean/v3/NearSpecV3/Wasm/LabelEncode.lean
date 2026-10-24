import NearSpec.ClaimCodec
import NearSpecV3.Wasm.Machine

/-!
# An injective byte encoding of `Label` and `Bool`

`Label` (`Machine.lean:208-213`) is the branch-label record carried inside every `Frame`:

```
structure Label where
  target : Nat
  arity  : Nat
  height : Nat
  isLoop : Bool
```

It is the third of the nine structure encoders (after `Val` and `Gas`), chosen next because
`Frame` needs it and it is the smallest remaining piece.

Encoding: three 8-byte little-endian words, then a **one-byte tag** for `isLoop` (0/1).

The `Bool` tag is worth separating out: `encBool`/`decBool` with
`decBool (encBool b ++ rest) = some (b, rest)` is the first *non-numeric* payload in the
serialiser, and it establishes the tag-byte idiom that `PRes`, `PromiseV` and `MAct` will all
need for their constructors.

## Bound hypothesis

As with `Val` and `Gas`, the round trip needs every `Nat` below `2^64`; that is `Label.wf`.
Branch targets and heights are code offsets and stack heights, both far below `2^64`.
-/

namespace NearSpecV3.Wasm

open NearSpec

/-- One-byte tag for a boolean. -/
def encBool (b : Bool) : Bytes := if b then [1] else [0]

/-- Read one tag byte. -/
def decBool : Bytes → Option (Bool × Bytes)
  | 0 :: rest => some (false, rest)
  | 1 :: rest => some (true, rest)
  | _ => none

theorem decBool_encBool (b : Bool) (rest : Bytes) :
    decBool (encBool b ++ rest) = some (b, rest) := by
  cases b <;> simp [encBool, decBool]

theorem encBool_inj {a b : Bool} (h : encBool a = encBool b) : a = b := by
  cases a <;> cases b <;> simp [encBool] at h ⊢

/-- Tag-free flat encoding: three words then the loop flag. -/
def Label.encode (l : Label) : Bytes :=
  leN 8 l.target ++ leN 8 l.arity ++ leN 8 l.height ++ encBool l.isLoop

/-- All three `Nat` fields fit in 64 bits. -/
def Label.wf (l : Label) : Prop :=
  l.target < 2^64 ∧ l.arity < 2^64 ∧ l.height < 2^64

/-- `step8` as in `GasEncode`: read one word then continue. Kept local so this module does
not depend on the gas file. -/
def lstep8 {α} (k : Nat → Bytes → Option α) (bs : Bytes) : Option α :=
  (NearSpec.readLE 8 bs).bind (fun p => k p.1 p.2)

/-- The decoder: three words then the loop tag, which must be the last byte.

Written as a `match` chain over `readLE`/`decBool` rather than via `lstep8`, because the
`bind`-style definition defeated type inference for the trailing `Option Label`. -/
def Label.decode (bs : Bytes) : Option Label :=
  match NearSpec.readLE 8 bs with
  | none => none
  | some q1 =>
    match NearSpec.readLE 8 q1.2 with
    | none => none
    | some q2 =>
      match NearSpec.readLE 8 q2.2 with
      | none => none
      | some q3 =>
        match decBool q3.2 with
        | none => none
        | some q4 =>
          if q4.2.isEmpty then some ⟨q1.1, q2.1, q3.1, q4.1⟩ else none

/-- The round trip on well-formed labels.

Strategy as for `Gas`: establish the whole decode result as one standalone `some (…)` fact
with `decide`-free rewriting, then `rw` it in. Rewriting *inside* the nested `match` does not
work (the arms absorb the rewrite), which is the obstruction documented in `GasEncode`. -/
theorem Label.decode_encode (l : Label) (h : l.wf) :
    Label.decode (l.encode) = some l := by
  obtain ⟨ht, ha, hh⟩ := h
  have hpow : (256 : Nat)^8 = 2^64 := by decide
  have h8 : ∀ n, n < 2^64 → n < 256^8 := fun n hn => by rw [hpow]; exact hn
  have e1 : NearSpec.readLE 8 (leN 8 l.target ++ (leN 8 l.arity ++ (leN 8 l.height ++ encBool l.isLoop)))
      = some (l.target, leN 8 l.arity ++ (leN 8 l.height ++ encBool l.isLoop)) :=
    NearSpec.readLE_append 8 l.target _ (h8 _ ht)
  have e2 : NearSpec.readLE 8 (leN 8 l.arity ++ (leN 8 l.height ++ encBool l.isLoop))
      = some (l.arity, leN 8 l.height ++ encBool l.isLoop) :=
    NearSpec.readLE_append 8 l.arity _ (h8 _ ha)
  have e3 : NearSpec.readLE 8 (leN 8 l.height ++ encBool l.isLoop)
      = some (l.height, encBool l.isLoop) :=
    NearSpec.readLE_append 8 l.height _ (h8 _ hh)
  have e4 : decBool (encBool l.isLoop) = some (l.isLoop, []) := by
    simpa using decBool_encBool l.isLoop []
  -- the decode body applied to the reassociated encoding, as a single fact
  have hgo : Label.decode (leN 8 l.target ++ (leN 8 l.arity ++ (leN 8 l.height ++ encBool l.isLoop)))
      = some l := by
    simp only [Label.decode, e1, e2, e3, e4, List.isEmpty_nil, if_true]
  have henc : l.encode =
      leN 8 l.target ++ (leN 8 l.arity ++ (leN 8 l.height ++ encBool l.isLoop)) := by
    simp [Label.encode, List.append_assoc]
  rw [henc, hgo]

/-- Injectivity follows because `decode` is a left inverse. -/
theorem Label.encode_injective {a b : Label} (ha : a.wf) (hb : b.wf)
    (h : a.encode = b.encode) : a = b := by
  have h1 := Label.decode_encode a ha
  have h2 := Label.decode_encode b hb
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

end NearSpecV3.Wasm
