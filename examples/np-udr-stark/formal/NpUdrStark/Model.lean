import ArenaCore.Verifier
import ZkFormal.Params

/-!
# PLACEHOLDER verifier model (`NpUdrStark.Model.verifier`)

Package skeleton only (lane L8). Lanes L4/L7 replace this file with the real
`np-udr-stark-v1` verifier, `(verifier nearAir prm).toVerifier`
(docs/zk-formal/DESIGN.md §7). Until then it REJECTS EVERYTHING, so the
skeleton can never accept a proof.

It imports `ZkFormal.Params` only to exercise the packaging of the zk-formal
package as candidate code in the model's import closure (formal/ZkFormal is
copied by build-recipe/sync-lean.sh); the build compiles that closure exactly
as the judge's native-lean build does.
-/

namespace NpUdrStark

/-- Reject-all placeholder; no oracle queries. -/
def Model.verifier : ArenaCore.OracleVerifier where
  run := fun _ hs _pub _cb _pb => (false, hs)

end NpUdrStark
