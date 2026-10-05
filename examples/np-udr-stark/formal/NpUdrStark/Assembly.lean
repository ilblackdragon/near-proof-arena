import NpUdrStark.Model
import NpUdrStark.PublicBin
import ZkFormal.NearAssembly.Closed

/-!
# `NpUdrStark.certificate_of`: the admission statement from the last two L6 inputs

The judge renders `ArenaExpected.expectedTypeFor model` as
`AdmissionStatement (challengeParamsWith (profileOf pid model tb [a0, a1] 40 64) fuel 8388608 rfuel)
  { publicDigest := pd, impl := .nativeTrusted bd tid model }`
(`spec/lean/judge/Expected.native-lean.lean.template`). `certificate_of` proves this for
`NpUdrStark.Model.verifier`, every judge literal of the validity-classical-128 profile, and
`pd = sha256 publicBin`, from L6's `RenderStmt` and `NearMinHeightStmt` (R-L7-6).
`NpUdrStark.Certificate` (added when L6 lands) is then a single application.
-/

namespace NpUdrStark

open ArenaCore NearSpec.TransferV1

theorem model_eq : Model.verifier = ZkFormal.NearAssembly.nearModel ZkFormal.Near.nearAir := rfl

theorem certificate_of (hR : ZkFormal.Near.RenderStmt) (hmin : ZkFormal.NearAssembly.NearMinHeightStmt)
    (pid model : String) (tb : Nat) (allowed : List String) (fuel rfuel : Nat)
    (pd bd : Digest) (tid : String)
    (hmodel : model = "random_oracle") (htb : tb ≤ 128)
    (hallowed : "random-oracle-fiat-shamir-sha256" ∈ allowed) (hpub : sha256 publicBin = pd) :
    AdmissionStatement
      (challengeParamsWith (profileOf pid model tb allowed 40 64) fuel 8388608 rfuel)
      { publicDigest := pd, impl := .nativeTrusted bd tid Model.verifier } :=
  ZkFormal.NearAssembly.near_certificate' hR hmin pid model tb allowed fuel rfuel publicBin pd bd tid
    hmodel htb hallowed hpub

end NpUdrStark
