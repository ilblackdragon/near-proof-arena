import ZkFormal.NearV3.Sched.Link.SoundSha
import ZkFormal.V2.KindReg

/-!
# `ShaKind` from the shared kind registry `KindReg`

The scheduler's kind-11 (`K_SCH`) ownership fact is an instance of `KindReg.avoid`: when kind 11
is registered only to the codec table `tc` and to no public segment, `ShaKind` holds.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

theorem shaKind_of_reg {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tc : Nat}
    {kinds : Nat → List Nat} {pubKinds : List Nat}
    (R : KindReg AP pub tr Fp.toNat ZkFormal.Near.B_BYTES kinds pubKinds)
    (hown : ∀ t, t ≠ tc → 11 ∉ kinds t) (hpub : 11 ∉ pubKinds) : ShaKind AP pub tr tc := by
  obtain ⟨h1, h2⟩ := R.avoid hown hpub
  exact ⟨h1, h2⟩

end ZkFormal.NearV3.Sched
