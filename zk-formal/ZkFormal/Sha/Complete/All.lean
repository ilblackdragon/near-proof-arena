import ZkFormal.Sha.Compose
import ZkFormal.Sha.Complete.Bool
import ZkFormal.Sha.Complete.Kind
import ZkFormal.Sha.Complete.IV
import ZkFormal.Sha.Complete.Round
import ZkFormal.Sha.Complete.Sched
import ZkFormal.Sha.Complete.Help
import ZkFormal.Sha.Complete.Digest
import ZkFormal.Sha.Complete.Frame
import ZkFormal.Sha.Complete.MultBits
import ZkFormal.Sha.Complete.Traffic

/-!
# ZkFormal.Sha.Complete.All — completeness of the SHA-256 table, closed

`Compose.sha_complete` instantiated with every completeness sublemma: the
honest trace of any supported list of messages satisfies the table (heights,
all 1011 constraints), its multiplicity bits are boolean, and its bus traffic
is exactly the messages' bytes and their `sha256` digests.
-/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra

theorem sha_complete_closed (msgs : List Gen.Msg) (hok : MsgsOk msgs) (t : Nat) (pub : List Fp) :
    ShaLocal (honestTrace msgs) t pub ∧
    (∀ r, r < (honestTrace msgs).height t → ∀ busBytes busDigest,
      ∀ i ∈ Table.interactions busBytes busDigest, ∀ b ∈ i.mult,
        b.eval (honestTrace msgs) t r pub = 0 ∨ b.eval (honestTrace msgs) t r pub = 1) ∧
    TrafficStmt :=
  sha_complete complete_cBool complete_cKind complete_cIV complete_cRound complete_cSched
    complete_cHelp complete_cDigest complete_cFrame logStmt multBitsStmt trafficStmt msgs hok t pub

end ZkFormal.Sha.Complete
