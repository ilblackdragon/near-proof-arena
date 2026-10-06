import NearSpecV3.WitnessV3

/-!
# Canonical witness bytes (executable; part of the verifier model)

A `near-arena-witness-v3` file is **canonical** when the three fields nearcore's
validator ignores are fixed: the chunk header's `height_included` is 0, its signature
is the all-zero ED25519 signature, and every `ChunkStateTransition.block_hash` is 32
zero bytes. The verifier accepts only canonical proofs, so no two accepted proofs of a
claim differ in bytes the relation does not read (`ADVERSARIAL_PROOFS`).
Definitions only (no proofs, no syntax extensions): the judge compiles this module.
-/

namespace ReexecV3D0

open NearSpec NearSpecV3

def zeroHash : Bytes := List.replicate 32 0

def zeros8 : Bytes := List.replicate 8 0

/-- ED25519 tag + 64 zero bytes. -/
def sig0 : Bytes := 0 :: List.replicate 64 0

/-- The header prefix of a state witness up to and including the signature:
returns (`height_included` bytes, signature bytes). -/
def hdrFields (bs : Bytes) : Except String (Bytes × Bytes) := do
  let (_, bs) ← pU8 "ChunkStateWitness tag" bs
  let (_, bs) ← pHash "epoch_id" bs
  let (_, bs) ← pU8 "ShardChunkHeader tag" bs
  let (_, bs) ← pChunkInner bs
  let (h, bs) ← pTake 8 "height_included" bs
  let (g, _) ← pSignature "chunk signature" bs
  pure (h, g)

/-- Canonical: the ignored header fields are zero and every transition block hash
is zero. (Decoding failures are not canonical.) -/
def canonicalSW (sw : Bytes) : Bool :=
  (match hdrFields sw with
   | .ok (h, g) => h == zeros8 && g == sig0
   | .error _ => false) &&
  (match decodeStateWitness sw with
   | .ok s => s.main.blockHash == zeroHash && s.implicit.all (·.blockHash == zeroHash)
   | .error _ => false)

/-- Canonical witness file: `near-arena-witness-v3`, no contract code, canonical
state witness. -/
def canonicalW (w : Bytes) : Bool :=
  match decodeWitnessFile w with
  | .ok (sw, []) => canonicalSW sw
  | _ => false

end ReexecV3D0
