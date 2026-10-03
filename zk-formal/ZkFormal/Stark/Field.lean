import ArenaCore

/-!
# ZkFormal.Stark.Field — what the protocol needs from the fields

The protocol model is written against an abstract pair of fields `F ⊆ K`
(BabyBear and its degree-8 binomial extension, lane L1) through the class
`StarkField`, so that L4 does not block on L1.  L1's executable types
`ZkFormal.Algebra.Fp` / `Fp8` instantiate it (one instance, no refinement:
L1's types are both the specification and the executable fields).

Everything in this file is *data* (executable); the algebraic facts the
soundness proof needs about these operations (ring homomorphism `embed`,
`ofLimbs ∘ limbs = id`, orders of `twoAdicGen`, …) are L1 lemmas about the
instance, stated in `StarkFieldLaws`.
-/

namespace ZkFormal.Stark

open ArenaCore Lean.Grind

/-- The BabyBear prime `15·2^27 + 1`. -/
def P : Nat := 2013265921

/-- Executable interface of the base field `F` and the extension `K`. -/
class StarkField (F : Type) (K : outParam Type) [Field F] [Field K] where
  /-- Canonical representative in `[0, P)`. -/
  toNat : F → Nat
  /-- The inclusion `F ⊆ K`. -/
  embed : F → K
  /-- The 8 coordinates of an extension element (`K = F[X]/(X^8 - 11)`,
  coefficient of `X^i` at index `i`); always length 8. -/
  limbs : K → List F
  /-- Inverse of `limbs` on lists of length 8 (missing limbs read as 0). -/
  ofLimbs : List F → K
  /-- Primitive `2^k`-th root of unity, `k ≤ 27`: `twoAdicGen27 ^ 2^(27-k)`
  with `twoAdicGen27 = 31^15`. -/
  twoAdicGen : Nat → F
  /-- The LDE coset shift of the largest domain: the multiplicative
  generator `31`. -/
  shift : F

/-- The laws the soundness/completeness proofs use (provided by L1). -/
class StarkFieldLaws (F : Type) (K : outParam Type) [Field F] [Field K] [StarkField F K] :
    Prop where
  embed_add : ∀ a b : F, StarkField.embed (a + b) = (StarkField.embed a + StarkField.embed b : K)
  embed_mul : ∀ a b : F, StarkField.embed (a * b) = (StarkField.embed a * StarkField.embed b : K)
  embed_one : (StarkField.embed (1 : F) : K) = 1
  embed_inj : ∀ a b : F, (StarkField.embed a : K) = StarkField.embed b → a = b
  limbs_length : ∀ x : K, (StarkField.limbs x : List F).length = 8
  ofLimbs_limbs : ∀ x : K, StarkField.ofLimbs (StarkField.limbs x : List F) = x
  toNat_lt : ∀ a : F, StarkField.toNat (K := K) a < P
  toNat_inj : ∀ a b : F, StarkField.toNat (K := K) a = StarkField.toNat (K := K) b → a = b
  natCast_toNat : ∀ a : F, @Nat.cast F Semiring.natCast (StarkField.toNat (K := K) a) = a

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

attribute [local instance] Semiring.natCast

/-- `n mod P` as a field element. -/
@[inline] def ofNatF (n : Nat) : F := (n : F)

/-- Canonical decoding of a 32-bit value: `none` unless `< P`. -/
@[inline] def decodeF? (n : Nat) : Option F := if n < P then some (n : F) else none

/-- 4-byte little-endian encoding of a base element (canonical). -/
def encF (a : F) : Bytes := Bytes.leN 4 (StarkField.toNat (K := K) a)

/-- 32-byte encoding of an extension element: its 8 limbs. -/
def encK (x : K) : Bytes := (StarkField.limbs x : List F).flatMap (encF (K := K))

/-- Big-endian 32-bit word `i` of a byte string. -/
def be32At (y : Bytes) (i : Nat) : Nat := Bytes.beToNat ((y.drop (4 * i)).take 4)

/-- Challenge decoding (DESIGN.md §4): 8 big-endian u32 limbs of the 32-byte
oracle answer, each reduced mod `P`.  At most `3^8` answers map to any
element of `K` (L1: `decodeChal_count`). -/
def decodeChal (y : Bytes) : K :=
  StarkField.ofLimbs ((List.range 8).map fun i => ofNatF (F := F) (be32At y i))

/-- Out-of-domain point decoding: as `decodeChal`, but if limbs `1..7` are
all zero, limb 1 is set to `1`; the result is never in `F` (DESIGN.md R4). -/
def decodeOod (y : Bytes) : K :=
  let ls := (List.range 8).map fun i => ofNatF (F := F) (be32At y i)
  if (ls.drop 1).all (fun a => decide (a = 0)) then
    StarkField.ofLimbs (ls.set 1 1)
  else StarkField.ofLimbs ls

/-- Bit reversal of the low `n` bits. -/
def bitrev (n x : Nat) : Nat := go n x 0
where
  go : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | k + 1, x, acc => go k (x / 2) (2 * acc + x % 2)

/-- Point of the LDE domain of size `2^n` at bit-reversed position `x`,
for the domain obtained by squaring the largest domain (size `2^n0`)
`n0 - n` times: `shift^(2^(n0-n)) · ω_n^(bitrev_n x)`. -/
def domPoint (n0 n x : Nat) : F :=
  (StarkField.shift (K := K) : F) ^ (2 ^ (n0 - n)) * (StarkField.twoAdicGen (K := K) n) ^ (bitrev n x)

end

end ZkFormal.Stark
