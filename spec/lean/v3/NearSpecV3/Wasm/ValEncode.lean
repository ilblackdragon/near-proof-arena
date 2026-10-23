import NearSpec.ClaimCodec
import NearSpecV3.Wasm.Machine

/-!
# An injective byte encoding of `Val` — **INCOMPLETE**

## What is done (proved, standard axioms only)

`Val.encode` (`Machine.lean:100-104`) is tag-dispatching so the four cases cannot collide:

| constructor | tag | payload |
|---|---:|---|
| `i32 v` | 0 | `leN 4 v.toNat` |
| `i64 v` | 1 | `leN 8 v.toNat` |
| `ref none` | 2 | — |
| `ref (some n)` | 3 | `borshBytes (leN (nb n) n)` |

and these two helper lemmas are fully proved, `[propext, Classical.choice, Quot.sound]`:

* `leN_inj`           — `leN w` determines its `Nat` argument on `x < 256^w`
* `leN4_uint32_inj`   — so `leN 4` determines a `UInt32`
* `leN8_uint64_inj`   — so `leN 8` determines a `UInt64`

## What is NOT done

**`Val.encode_injective` is not proved.** It contains one `sorry`, and
`#print axioms Val.encode_injective` reports `sorryAx`, so the result must not be cited as a
theorem. The missing step is `encNatFull_inj`:

```
encNatFull n = encNatFull m  →  n = m
```

which needs `lt_pow_nb : n < 256 ^ (nb n)` — the claim that the minimal little-endian byte
count `nb n` really is enough to represent `n`. That is a straightforward induction on `n`
via `Nat.div_add_mod`, but my attempts did not close it before I stopped, and I would
rather leave the gap visible than paper over it.

`i32`, `i64` and `ref none` cases *are* discharged; only `ref (some _)` depends on the
`sorry`.

## Why this file is still worth keeping

The tag scheme and the three payload lemmas are the reusable part: `Gas`, `Frame`,
`CallCtx`, `PRes`, `PromiseV`, `MAct`, `RealStore` and `St` will all need the same pattern,
and the `Nat`-unboundedness problem (`ref (some n)` cannot use `leN 8`) is a real design
constraint discovered here rather than in the middle of a larger proof.
-/

namespace NearSpecV3.Wasm

open NearSpec

/-- Minimal byte count of `n` in little-endian. -/
def nb : Nat → Nat
  | 0 => 0
  | n + 1 => nb ((n + 1) / 256) + 1

/-- Full (unbounded) `Nat` encoding: a 4-byte length then `nb n` little-endian bytes.
`ref (some n)` carries an unbounded `Nat`, which `leN 8` would silently truncate, so the
payload is length-delimited. `nb` (not `leN`'s fixed width) is what makes the length enough
to recover `n`: `leNat (leN (nb n) n) = n` because `n < 256^(nb n)`. -/
def encNatFull (n : Nat) : Bytes := borshBytes (leN (nb n) n)

/-- Tag-dispatching, length-unambiguous encoding of one operand. -/
def Val.encode : Val → Bytes
  | .i32 v => [0] ++ leN 4 v.toNat
  | .i64 v => [1] ++ leN 8 v.toNat
  | .ref none => [2]
  | .ref (some n) => [3] ++ encNatFull n

/-- `leN` is determined by its `Nat` argument on the range it encodes. -/
theorem leN_inj {w a b : Nat} (h : leN w a = leN w b) (ha : a < 256^w) (hb : b < 256^w) :
    a = b := by
  have h1 : leNat (leN w a) = a := leNat_leN w a ha
  have h2 : leNat (leN w b) = b := leNat_leN w b hb
  rw [h] at h1
  omega

/-- `leN 4` determines a `UInt32`. -/
theorem leN4_uint32_inj {a b : UInt32} (h : leN 4 a.toNat = leN 4 b.toNat) : a = b := by
  have ha : a.toNat < 256^4 := by
    have : (256:Nat)^4 = 2^32 := by decide
    rw [this]; exact a.toNat_lt
  have hb : b.toNat < 256^4 := by
    have : (256:Nat)^4 = 2^32 := by decide
    rw [this]; exact b.toNat_lt
  exact UInt32.toNat_inj.mp (leN_inj h ha hb)

/-- `leN 8` determines a `UInt64`. -/
theorem leN8_uint64_inj {a b : UInt64} (h : leN 8 a.toNat = leN 8 b.toNat) : a = b := by
  have ha : a.toNat < 256^8 := by
    have : (256:Nat)^8 = 2^64 := by decide
    rw [this]; exact a.toNat_lt
  have hb : b.toNat < 256^8 := by
    have : (256:Nat)^8 = 2^64 := by decide
    rw [this]; exact b.toNat_lt
  exact UInt64.toNat_inj.mp (leN_inj h ha hb)

/-- The encoding is injective: distinct operands have distinct encodings.

Proof shape: split on both constructors and, for `ref`, on the payload option *first*, so
`Val.encode` reduces to a literal byte list and `h` becomes a list equality between distinct
leading tags (closed by `simp`) or between identical tags (payload extracted by `simpa`). -/
theorem Val.encode_injective {a b : Val} (h : a.encode = b.encode) : a = b := by
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
      cases b with
      | i32 v => simp only [Val.encode] at h; simp at h
      | i64 v => simp only [Val.encode] at h; simp at h
      | ref s =>
        cases s with
        | none => simp only [Val.encode] at h; simp at h
        | some m =>
          have hp : encNatFull n = encNatFull m := by
            simp only [Val.encode] at h; simpa using h
          -- NOT PROVED: encNatFull_inj (see the file header). Left as an explicit goal so
          -- the omission is visible rather than hidden behind a tactic failure.
          have hnm : n = m := by
            sorry
          rw [hnm]

end NearSpecV3.Wasm
