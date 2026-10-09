import ZkFormal.NearV3.Candidates.SchedField
import ZkFormal.NearV3.Sched.Complete.ProcRows
namespace ZkFormal.NearV3.Candidates.ProcKeyInverse
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

theorem difference_zero (a b : Nat) (ha : a<P) (hb : b<P) :
    fsub a b % P = 0 ↔ a=b := by
  unfold fsub
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb,Nat.mod_mod]
  unfold P at *
  omega

theorem key_inverse (k : Nat) (hk : k<16) :
    (Fp.ofNat k + -(15 : Fp)) * Fp.ofNat (if k=15 then 0 else finv (fsub k 15)) =
      1 - (if k=15 then (1 : Fp) else 0) := by
  by_cases he : k=15
  · subst k
    simp only [ite_true]
    change ((15 : Fp) + -15) * 0 = 1-1
    grind
  · rw [if_neg he,if_neg he]
    have hz : fsub k 15 % P ≠ 0 := by
      intro h
      exact he ((difference_zero k 15 (by unfold P; omega) (by decide)).1 h)
    have h := SchedField.inverse_product (fsub k 15)
    rw [if_neg hz,SchedField.fsub_cast] at h
    change (Fp.ofNat k - (15 : Fp)) * Fp.ofNat (finv (fsub k 15)) = 1 at h
    grind

/-- The native `kc=15` flag also annihilates the tested difference. -/
theorem key_flag (k : Nat) :
    (Fp.ofNat k + -(15 : Fp)) * Fp.ofNat (b2n (k==15)) = 0 := by
  by_cases he : k=15
  · subst k
    change ((15 : Fp) + -15) * 1=0
    grind
  · have hb : b2n (k==15)=0 := by simp [b2n,he]
    rw [hb]
    change _ * (0 : Fp)=0
    grind
end ZkFormal.NearV3.Candidates.ProcKeyInverse
