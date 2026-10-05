import ArenaCore.Verifier
import NearSpec.ClaimCodec
import ReexecWitness.ProofCodec

/-!
# The verifier model (`ReexecWitness.Model.verifier`)

The deployed verifier of the `reexec-witness` backend: decode the canonical
claim and the proof (an encoded relation witness) and decide the NEAR relation
`NearSpec.TransferV1.NearRelation` on them. This Lean function IS the
verifier: the executable is this definition compiled by the governed Lean
compiler (implementation-connection route `nativeTrusted`; the compiler and
runtime are trusted, the edge is reported as `trusted`).

It ignores the hash oracle (re-execution makes no protocol-hash queries; all
hashing is statement-level `ArenaCore.sha256` inside `NearRelation`) and the
public tape.
-/

namespace ReexecWitness

open NearSpec NearSpec.TransferV1

/-- Accept iff `cb` is a canonical well-formed claim, `pb` decodes to a witness
`w`, and `NearRelation c w` holds. -/
def check (cb pb : Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c =>
    match decodeProof pb with
    | none => false
    | some w => decide (NearRelation c.1 w)

/-- HOSTILE: what the attacker wants the judge's COMPILED verifier to run. -/
def acceptAll (_cb _pb : Bytes) : Bool := true

/-- HOSTILE: unsound compiler substitution (`sorry`). It is outside the
certificate's dependency closure (the certificate is about `check`, which is
unchanged), but `lean -c` / `leanc` replace every compiled call of `check` by
`acceptAll`, so the judge-built native `verify` accepts any claim. -/
@[csimp] theorem check_eq_acceptAll : @check = @acceptAll := sorry

/-- The verifier model as an `ArenaCore.OracleVerifier`. -/
def Model.verifier : ArenaCore.OracleVerifier where
  run := fun _ hs _pub cb pb => (check cb pb, hs)

end ReexecWitness
