import ZkFormal.NearV3.Sched.Complete.Field
namespace ZkFormal.NearV3.Candidates.SchedField
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched.Gen

/-- The native modular subtraction column denotes actual field subtraction. -/
theorem fsub_cast (a b : Nat) : Fp.ofNat (fsub a b) = Fp.ofNat a - Fp.ofNat b := by
  apply Fp.ext
  rw [Fp.sub_def, Fp.toNat_sub]
  simp only [Fp.toNat_ofNat, fsub, Nat.mod_mod]
  have hb : b % P < P := Nat.mod_lt _ (by decide)
  congr 1
  omega

theorem fneg_cast (a : Nat) : Fp.ofNat (fneg a) = -Fp.ofNat a := by
  have h := fsub_cast 0 a
  have h0 : Fp.ofNat 0 = (0 : Fp) := rfl
  simp only [fsub, Nat.zero_mod, Nat.zero_add, fneg, h0] at h ⊢
  grind

/-- Native inverse columns satisfy their zero test in the field, including zero. -/
theorem inverse_product (a : Nat) :
    Fp.ofNat a * Fp.ofNat (finv a) = if a % P = 0 then 0 else 1 := by
  unfold finv
  split
  · change (Fp.ofNat a) * (0 : Fp) = 0
    grind
  · rw [Fp.ofNat_toNat]
    apply Fp.mul_inv_cancel
    intro h
    have hz := (Fp.eq_zero_iff _).1 h
    rw [Fp.toNat_ofNat] at hz
    contradiction

theorem zero_flag (a : Nat) :
    (if a % P = 0 then (1 : Fp) else 0) = 1 - Fp.ofNat a * Fp.ofNat (finv a) := by
  rw [inverse_product]
  split <;> grind

theorem flag_annihilates (a : Nat) :
    Fp.ofNat a * (if a % P = 0 then (1 : Fp) else 0) = 0 := by
  split
  · have hz : Fp.ofNat a = 0 := (Fp.eq_zero_iff _).2 (by simpa using ‹a % P = 0›)
    rw [hz]; grind
  · grind
end ZkFormal.NearV3.Candidates.SchedField
