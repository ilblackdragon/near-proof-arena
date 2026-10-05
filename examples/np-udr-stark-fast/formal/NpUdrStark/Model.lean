import ZkFormal.Near.Air
import ZkFormal.Assembly.Guard
import ZkFormal.Stark.Verifier
import ZkFormal.Stark.Instance
import NearSpec.Challenge

/-!
# The deployed verifier model `NpUdrStark.Model.verifier`

`np-udr-stark-v1` for `near-transfer-receipt-v1`: the claim-canonicality guard
(`Assembly.claimOk`, R-L7-2) followed by lane L4's BCS-compiled verifier
`ZkFormal.Stark.verifier Fp Fp8 nearAir Params.default` (BabyBear / `F_p^8`,
24 chunks × 9 positions, minimum query domain 2^8, oracle answers normalised by
`fit32`). It is definitionally `ZkFormal.NearAssembly.nearModel nearAir`
(`NpUdrStark.model_eq`, by `rfl`), the model `near_certificate'` is about.

The judge compiles exactly this definition (native-lean route). Its import closure
holds only trusted modules (ArenaCore, NearSpec.Challenge and its imports) and
`formal/ZkFormal` modules, with no `Lean`/`Std`. The `@[csimp]` fast paths
(`Stark.take?_eq_takeF`, `readInj_eq_readInjF`, `mpLeaves_eq_mpLeavesF`) are
kernel-proved and audited by the checker (R-L7-5).
-/

namespace NpUdrStark

open ArenaCore ZkFormal ZkFormal.Stark ZkFormal.Algebra

def Model.verifier : OracleVerifier :=
  (Assembly.guardTree (Assembly.claimOk NearSpec.TransferV1.challengeSpec)
    (ZkFormal.Stark.verifier Fp Fp8 ZkFormal.Near.nearAir Params.default)).toVerifier

end NpUdrStark
