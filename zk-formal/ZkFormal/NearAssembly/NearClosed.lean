import ZkFormal.NearAssembly.Closed
import ZkFormal.NearAssembly.MinHeight
import ZkFormal.Near.Render.Proof.Main

/-!
# ZkFormal.NearAssembly.NearClosed — NEAR admission with every L6 obligation discharged

`RenderStmt` (`Render.render_stmt_closed`) and `NearMinHeightStmt` (`near_min_height`).
-/

namespace ZkFormal.NearAssembly

open ArenaCore NearSpec.TransferV1 ZkFormal.Near

theorem near_certificate_closed
    (pid model : String) (tb : Nat) (allowed : List String) (fuel rfuel : Nat)
    (pub : ArenaCore.Bytes) (pd bd : ArenaCore.Digest) (tid : String)
    (hmodel : model = "random_oracle") (htb : tb ≤ 128)
    (hallowed : "random-oracle-fiat-shamir-sha256" ∈ allowed) (hpub : ArenaCore.sha256 pub = pd) :
    AdmissionStatement
      (challengeParamsWith (profileOf pid model tb allowed 40 64) fuel 8388608 rfuel)
      { publicDigest := pd, impl := .nativeTrusted bd tid (nearModel nearAir) } :=
  near_certificate' Render.render_stmt_closed near_min_height pid model tb allowed fuel rfuel pub pd bd tid
    hmodel htb hallowed hpub

end ZkFormal.NearAssembly
