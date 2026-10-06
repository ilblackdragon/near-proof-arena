import ArenaCore.Verifier
import NearSpecV3.ChallengeD2
import ReexecV3D2.NormBytesDefs

/-!
# The verifier model (`ReexecV3D2.Model.verifier`)

The deployed verifier of the `reexec-v3-d2` backend for
`near/pv86/chunk-validation/v0`, domain D2: decode the canonical claim
(`near-arena-claim-v3`, well-formed) and decide the challenge relation
`RelD2 (encode c) pb` with the proof bytes `pb` as the witness
(`near-arena-witness-v3`: the real nearcore `ChunkStateWitness` borsh, in normal
form). This
Lean function IS the verifier: the executable is this definition compiled by
the governed Lean compiler (implementation-connection route `nativeTrusted`;
the compiler and runtime are trusted, the edge is reported as `trusted`).

It ignores the hash oracle (re-execution makes no protocol-hash queries; all
hashing is statement-level `ArenaCore.sha256` inside `RelD2`) and the public
tape.
-/

namespace ReexecV3D2

open NearSpecV3

/-- Accept iff `cb` decodes to a well-formed v3 claim `c`, the proof is a witness file in
**normal form** (`normalW`, `NormBytesDefs`: a fixed point of the normaliser — the
validator-ignored `height_included`, chunk signature and transition block hashes are
zero, the receipt-proof map has one entry per key in increasing key order, and every
`base_state` holds exactly the trie values the relation's full reveal looks up, without duplicates, in
byte order — so no two accepted proofs of a claim differ in a degree of freedom the
validator's lenient decoding leaves), and `RelD2 (encode c) pb`. -/
def check (cb pb : ArenaCore.Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c => normalW c.encode pb && decide (RelD2 c.encode pb)

/-- The verifier model as an `ArenaCore.OracleVerifier`. -/
def Model.verifier : ArenaCore.OracleVerifier where
  run := fun _ hs _pub cb pb => (check cb pb, hs)

end ReexecV3D2
