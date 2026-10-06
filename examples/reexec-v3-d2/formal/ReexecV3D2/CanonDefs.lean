import NearSpecV3.WitnessV3

/-!
# Fixed values of the validator-ignored witness fields (executable; part of the verifier model)

nearcore's validator (hence `RelD2`) never reads three witness fields: the chunk header's
`height_included`, its signature, and every `ChunkStateTransition.block_hash`. In the normal
form they are `0`, the all-zero ED25519 signature `sig0` and 32 zero bytes.
Definitions only (no proofs, no syntax extensions): the judge compiles this module.
-/

namespace ReexecV3D2

open NearSpec NearSpecV3

def zeroHash : Bytes := List.replicate 32 0

def zeros8 : Bytes := List.replicate 8 0

/-- ED25519 tag + 64 zero bytes. -/
def sig0 : Bytes := 0 :: List.replicate 64 0

end ReexecV3D2
