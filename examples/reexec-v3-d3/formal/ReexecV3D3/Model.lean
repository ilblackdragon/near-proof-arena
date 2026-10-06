import ArenaCore.Verifier
import NearSpecV3.ChallengeChunkV3
import ReexecV3D3.Canon

/-!
# The verifier model (`ReexecV3D3.Model.verifier`)

The deployed verifier of the `reexec-v3-d3` backend for `near/pv86/chunk-validation/v0`, domain
D3α: decode the canonical claim (`near-arena-claim-v3`, well-formed), require the proof to be a
witness file in **normal form** (`normalW`, `Canon.lean`: ignored header fields zeroed, receipt
proofs one per key in key order, the main store and every implicit store exactly their *necessary*
values — one per hash, byte order, dropping any one makes `checkD3` reject — with the main values
`revealAll` looks up as `base_state` and the rest as contract code), and decide `RelD3 (encode c) pb`
(`NearSpecV3.D3.checkD3`). This Lean function IS the verifier: the executable is this definition
compiled by the governed Lean compiler (route `native-lean`, implementation connection `trusted`).

It ignores the hash oracle (re-execution makes no protocol-hash queries) and the public tape.
-/

namespace ReexecV3D3

open NearSpecV3

def check (cb pb : ArenaCore.Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c => normalW c.encode pb && acceptsD3 c.encode pb

/-- The verifier model as an `ArenaCore.OracleVerifier`. -/
def Model.verifier : ArenaCore.OracleVerifier where
  run := fun _ hs _pub cb pb => (check cb pb, hs)

end ReexecV3D3
