import ZkFormal.NearAssembly.Final
import ZkFormal.Prover.SizeBoundNear

/-!
# ZkFormal.NearAssembly.Closed — M5 with the size bound discharged

`near_certificate'`: the NEAR admission statement from **only** L6's `RenderStmt` and
`NearMinHeightStmt` (R-L7-6).  The proof-size bound is `SizeBound.near_size`
(header-free bound `sizeMax nearAir default 86 = 7 426 175 ≤ 8 MiB`).
-/

namespace ZkFormal.NearAssembly

open ArenaCore NearSpec.TransferV1 ZkFormal.Near

theorem near_certificate' (hR : RenderStmt) (hmin : NearMinHeightStmt)
    (pid model : String) (tb : Nat) (allowed : List String) (fuel rfuel : Nat)
    (pub : ArenaCore.Bytes) (pd bd : ArenaCore.Digest) (tid : String)
    (hmodel : model = "random_oracle") (htb : tb ≤ 128)
    (hallowed : "random-oracle-fiat-shamir-sha256" ∈ allowed) (hpub : ArenaCore.sha256 pub = pd) :
    AdmissionStatement
      (challengeParamsWith (profileOf pid model tb allowed 40 64) fuel 8388608 rfuel)
      { publicDigest := pd, impl := .nativeTrusted bd tid (nearModel nearAir) } :=
  near_certificate hR hmin Prover.SizeBound.near_size pid model tb allowed fuel rfuel pub pd bd tid
    hmodel htb hallowed hpub

end ZkFormal.NearAssembly
