import ArenaCore.Admission

/-!
# Toy — a worked example (NOT NEAR)

**Toy relation (table lookup).**  The challenge fixes a 4-byte table
`toyTable`.  A claim is a pair `(i, v)` of bytes, encoded as the two bytes
`[i, v]`; it is true iff `toyTable[i] = v`.  The witness is trivial.

The verifier does *not* know the table: its public artifact is only
`sha256 toyTable`.  A proof is a table `T'`; the verifier accepts iff
`sha256 T' = pub` and `T'[i] = v`.  Soundness therefore genuinely depends on
SHA-256 collision resistance: an accepted false claim yields
`T' ≠ toyTable` with equal hashes.  This is the smallest example exercising
every part of the admission statement: the interpreter route, the claim
codec, completeness, and an explicit fuel-bounded reduction to collisions.
-/

namespace Toy

open ArenaCore

/-- The table fixed by the toy challenge ("ARNA"). -/
def toyTable : Bytes := [0x41, 0x52, 0x4E, 0x41]

/-- Toy claims: (index, value). -/
abbrev ToyClaim := UInt8 × UInt8

def toyDecode : Bytes → Option ToyClaim
  | [i, v] => some (i, v)
  | _ => none

def toyEncode (c : ToyClaim) : Bytes := [c.1, c.2]

/-- The toy challenge relation. -/
def ToyRel (c : ToyClaim) (_ : Unit) : Prop := toyTable[c.1.toNat]? = some c.2

def toySpec : ChallengeSpec where
  Claim := ToyClaim
  Witness := Unit
  Rel := ToyRel
  Domain := fun _ => True
  decodeClaim := toyDecode
  encodeClaim := toyEncode
  decode_encode := fun _ => rfl

/-- A standard-model profile allowing `sha256_cr`, 128-bit target. -/
def toyProfile : SecurityProfile where
  id := "toy-validity-classical-128"
  model := .standard
  targetBits := 128
  allowedAssumptions := [.sha256CollisionResistance]
  maxProverQueriesLog2 := 20
  maxHashQueriesLog2 := 64

def toyParams : ChallengeParams where
  spec := toySpec
  profile := toyProfile
  verifyFuel := 10000
  maxProofBytes := 256
  maxReductionFuel := 10000

end Toy
