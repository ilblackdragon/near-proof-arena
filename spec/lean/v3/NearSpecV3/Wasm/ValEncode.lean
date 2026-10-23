import NearSpec.ClaimCodec
import NearSpecV3.Wasm.Machine

/-!
# An injective byte encoding of `Val`

`Val` (`Machine.lean:100-104`) is the operand type:

```
inductive Val where
  | i32 (v : UInt32)
  | i64 (v : UInt64)
  | ref (r : Option Nat)
```

The encoding is tag-dispatching, so the four cases can never collide:

| constructor | tag | payload |
|---|---:|---|
| `i32 v` | 0 | `leN 4 v.toNat` |
| `i64 v` | 1 | `leN 8 v.toNat` |
| `ref none` | 2 | — |
| `ref (some n)` | 3 | `leN 8 n` |

## The `ref` bound, and why a hypothesis is the right shape

`ref (some n)` carries a `Nat`, but `leN 8` truncates to the low 64 bits, so the encoding is
only injective for `n < 2^64`. Rather than making the wire format unbounded — an earlier
attempt used a length-delimited `Nat` encoding and needed a divergence induction that I could
not close — the theorem takes the bound as a **hypothesis**, exactly as
`NearSpec.Claim.encode_injective` (`ClaimCodec.lean:127`) takes `c.wf = true`.

That is the right shape here too: a table index is bounded by `maxTableElementsStore = 10000`
(`Machine.lean:99`) and a table's size by `tableMax` (enforced at `Exec.lean:243`), so real
machine states satisfy the bound by construction. The bound is not an extra assumption about
the machine; it is a fact about it, made explicit at the interface.

## Provenance

Three earlier attempts at this file are worth recording so they are not repeated:
1. proving `leNat_leN` from scratch → the library build failed, it already exists (stronger)
2. `simp only [...] at h` on the tag equality → the `++` is not peeled; `simpa using h`
   after `simp only [Val.encode] at h` is what works
3. unbounded `Nat` payload → needs `n < 256^(nb n)`, a divergence induction; the bound
   hypothesis removes the need entirely
-/

namespace NearSpecV3.Wasm

open NearSpec

/-- Tag-dispatching encoding of one operand. Injective on `ref` for `n < 2^64`. -/
def Val.encode : Val → Bytes
  | .i32 v => [0] ++ leN 4 v.toNat
  | .i64 v => [1] ++ leN 8 v.toNat
  | .ref none => [2]
  | .ref (some n) => [3] ++ leN 8 n

/-- `leN w` determines its `Nat` argument on the range it can represent. -/
theorem leN_inj {w a b : Nat} (h : leN w a = leN w b) (ha : a < 256^w) (hb : b < 256^w) :
    a = b := by
  have h1 : leNat (leN w a) = a := leNat_leN w a ha
  have h2 : leNat (leN w b) = b := leNat_leN w b hb
  rw [h] at h1
  omega

/-- `leN 4` determines a `UInt32`. -/
theorem leN4_uint32_inj {a b : UInt32} (h : leN 4 a.toNat = leN 4 b.toNat) : a = b := by
  have hp : (256 : Nat)^4 = 2^32 := by decide
  exact UInt32.toNat_inj.mp
    (leN_inj h (by rw [hp]; exact a.toNat_lt) (by rw [hp]; exact b.toNat_lt))

/-- `leN 8` determines a `UInt64`. -/
theorem leN8_uint64_inj {a b : UInt64} (h : leN 8 a.toNat = leN 8 b.toNat) : a = b := by
  have hp : (256 : Nat)^8 = 2^64 := by decide
  exact UInt64.toNat_inj.mp
    (leN_inj h (by rw [hp]; exact a.toNat_lt) (by rw [hp]; exact b.toNat_lt))

/-- Well-formed operand: a `ref` index fits in 64 bits. Real machine states satisfy this
(`maxTableElementsStore = 10000`, `tableMax` enforced at `Exec.lean:243`). -/
def Val.wf : Val → Prop
  | .i32 _ => True
  | .i64 _ => True
  | .ref none => True
  | .ref (some n) => n < 2^64

/-- The encoding is injective on well-formed operands.

Cross-constructor cases are closed by the distinct leading tag; same-constructor cases
extract the `leN` payload with `simpa` and apply the corresponding `leN*_inj`. -/
theorem Val.encode_injective {a b : Val} (ha : a.wf) (hb : b.wf) (h : a.encode = b.encode) :
    a = b := by
  cases a with
  | i32 x =>
    cases b with
    | i32 y =>
      have hp : leN 4 x.toNat = leN 4 y.toNat := by
        simp only [Val.encode] at h; simpa using h
      exact congrArg Val.i32 (leN4_uint32_inj hp)
    | i64 v => simp only [Val.encode] at h; simp at h
    | ref r => cases r <;> (simp only [Val.encode] at h; simp at h)
  | i64 x =>
    cases b with
    | i32 v => simp only [Val.encode] at h; simp at h
    | i64 y =>
      have hp : leN 8 x.toNat = leN 8 y.toNat := by
        simp only [Val.encode] at h; simpa using h
      exact congrArg Val.i64 (leN8_uint64_inj hp)
    | ref r => cases r <;> (simp only [Val.encode] at h; simp at h)
  | ref r =>
    cases r with
    | none =>
      cases b with
      | i32 v => simp only [Val.encode] at h; simp at h
      | i64 v => simp only [Val.encode] at h; simp at h
      | ref s => cases s <;> (simp only [Val.encode] at h; simp_all)
    | some n =>
      simp only [Val.wf] at ha
      cases b with
      | i32 v => simp only [Val.encode] at h; simp at h
      | i64 v => simp only [Val.encode] at h; simp at h
      | ref s =>
        cases s with
        | none => simp only [Val.encode] at h; simp at h
        | some m =>
          simp only [Val.wf] at hb
          have hp : leN 8 n = leN 8 m := by
            simp only [Val.encode] at h; simpa using h
          have hpow : (256 : Nat)^8 = 2^64 := by decide
          have hnm : n = m :=
            leN_inj hp (by rw [hpow]; exact ha) (by rw [hpow]; exact hb)
          rw [hnm]

-- Round trip (added): a decoder for the tag-dispatching encoding, carrying the remainder.
-- This is the form `Frame` needs, since `Val.encode` elements are concatenated in an array.

/-- Decode one operand, returning the remainder. -/
def Val.decode : Bytes → Option (Val × Bytes)
  | 0 :: rest => (NearSpec.readLE 4 rest).map (fun p => (Val.i32 (UInt32.ofNat p.1), p.2))
  | 1 :: rest => (NearSpec.readLE 8 rest).map (fun p => (Val.i64 (UInt64.ofNat p.1), p.2))
  | 2 :: rest => some (Val.ref none, rest)
  | 3 :: rest => (NearSpec.readLE 8 rest).map (fun p => (Val.ref (some p.1), p.2))
  | _ => none

/-- Decoding an encoded well-formed operand returns it unchanged, with the remainder. -/
theorem Val.decode_encode (v : Val) (h : v.wf) (rest : Bytes) :
    Val.decode (v.encode ++ rest) = some (v, rest) := by
  cases v with
  | i32 x =>
    have hx : x.toNat < 256^4 := by
      have hp : (256 : Nat)^4 = 2^32 := by decide
      rw [hp]; exact x.toNat_lt
    simp only [Val.encode, Val.decode, List.cons_append, List.nil_append]
    rw [NearSpec.readLE_append 4 x.toNat rest hx]
    simp [UInt32.ofNat_toNat]
  | i64 x =>
    have hx : x.toNat < 256^8 := by
      have hp : (256 : Nat)^8 = 2^64 := by decide
      rw [hp]; exact x.toNat_lt
    simp only [Val.encode, Val.decode, List.cons_append, List.nil_append]
    rw [NearSpec.readLE_append 8 x.toNat rest hx]
    simp [UInt64.ofNat_toNat]
  | ref r =>
    cases r with
    | none => simp [Val.encode, Val.decode]
    | some n =>
      simp only [Val.wf] at h
      have hn : n < 256^8 := by
        have hp : (256 : Nat)^8 = 2^64 := by decide
        rw [hp]; exact h
      simp only [Val.encode, Val.decode, List.cons_append, List.nil_append]
      rw [NearSpec.readLE_append 8 n rest hn]
      simp

end NearSpecV3.Wasm
