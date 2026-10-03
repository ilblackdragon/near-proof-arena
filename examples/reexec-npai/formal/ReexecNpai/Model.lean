import ArenaCore.Verifier
import NearSpec.ClaimCodec
import ReexecNpai.Codec

/-!
# The reference model of the `reexec-npai` verifier

`check cb pb` decodes the canonical claim and the proof (format
`reexec-npai-v1`, `Codec.lean`) and decides the NEAR relation. The deployed
verifier is NPAI bytecode, not this function; `Main.lean` proves that the
bytecode computes exactly `check` (within the challenge fuel).
-/

namespace ReexecNpai

open NearSpec NearSpec.TransferV1

def check (cb pb : Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c =>
    match decodeProof pb with
    | none => false
    | some w => decide (NearRelation c.1 w)

end ReexecNpai
