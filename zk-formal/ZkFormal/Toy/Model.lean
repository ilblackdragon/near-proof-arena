import ZkFormal.Toy.AirDef
import ZkFormal.Assembly.Guard
import ZkFormal.Stark.Verifier
import ZkFormal.Stark.Instance
import ZkToySpec

/-!
# ZkFormal.Toy.Model — the deployed verifier model of the M2 toy candidate

`verifier`: the claim guard (`claimOk`) followed by L4's BCS-compiled np-udr-stark
verifier for `toyAir` over BabyBear / `F_p^8`, with the default parameters.  On the
native-lean route the judge compiles exactly this definition.
-/

namespace ZkFormal.Toy.Model

open ArenaCore ZkFormal.Stark ZkFormal.Algebra

def verifier : OracleVerifier :=
  (Assembly.guardTree (Assembly.claimOk ZkToySpec.challengeSpec)
    (ZkFormal.Stark.verifier Fp Fp8 toyAir Params.default)).toVerifier

end ZkFormal.Toy.Model
