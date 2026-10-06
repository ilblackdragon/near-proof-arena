import ArenaCore.Verifier
import NearSpecV3.ChallengeV3
import ReexecV3D0.CanonDefs

/-!
# The verifier model (`ReexecV3D0.Model.verifier`)

The deployed verifier of the `reexec-v3-d0` backend for
`near/pv86/chunk-validation/v0`, domain D0: decode the canonical claim
(`near-arena-claim-v3`, well-formed) and decide the challenge relation
`RelD0 (encode c) pb` with the proof bytes `pb` as the witness
(`near-arena-witness-v3`: the real nearcore `ChunkStateWitness` borsh, in canonical
form). This
Lean function IS the verifier: the executable is this definition compiled by
the governed Lean compiler (implementation-connection route `nativeTrusted`;
the compiler and runtime are trusted, the edge is reported as `trusted`).

It ignores the hash oracle (re-execution makes no protocol-hash queries; all
hashing is statement-level `ArenaCore.sha256` inside `RelD0`) and the public
tape.
-/

namespace ReexecV3D0

open NearSpecV3

/-- Accept iff `cb` decodes to a well-formed v3 claim `c`, the proof is a **canonical**
witness file (`canonicalW`: the validator-ignored `height_included`, chunk signature and
transition block hashes are zero, so no two accepted proofs of a claim differ only in
bytes the relation ignores), and `RelD0 (encode c) pb`. -/
def check (cb pb : ArenaCore.Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c => canonicalW pb && decide (RelD0 c.encode pb)

/-- The verifier model as an `ArenaCore.OracleVerifier`. -/
def Model.verifier : ArenaCore.OracleVerifier where
  run := fun _ hs _pub cb pb => (check cb pb, hs)

end ReexecV3D0
