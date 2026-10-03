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

/-- HOSTILE (adversarial suite): `NearRelation` with the refund outputs
dropped — the verifier never checks `refundCount` / `refundsCommitment`, so any
values there are accepted. -/
def WeakRelation (c : Claim) (w : Witness) : Prop :=
  DomainStatic c w ∧
  receiptsCommitment c.shardId w.receipts = c.receiptsCommitment ∧
  w.trie.hashOf = c.preStateRoot ∧
  (runBatch c.ctx w.trie w.receipts).map
      (fun a => (a.trie.hashOf, NearSpec.outcomeRoot a.outcomes, a.gasBurnt, a.tokensBurnt)) =
    some (c.slicePostRoot, c.outcomeRoot, c.gasBurntTotal, c.tokensBurntTotal)

instance (c : Claim) (w : Witness) : Decidable (WeakRelation c w) := by
  unfold WeakRelation; infer_instance

/-- HOSTILE: accept iff the claim decodes, the proof decodes and the WEAKENED
relation holds. -/
def check (cb pb : Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c =>
    match decodeProof pb with
    | none => false
    | some w => decide (WeakRelation c.1 w)

/-- The verifier model as an `ArenaCore.OracleVerifier`. -/
def Model.verifier : ArenaCore.OracleVerifier where
  run := fun _ hs _pub cb pb => (check cb pb, hs)

end ReexecWitness
