import ZkFormal.NearV3.Candidates.SchedField
import ZkFormal.NearV3.Sched.Tables.Codec
namespace ZkFormal.NearV3.Candidates.CodecZeroTest
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
/-- The codec's three zero-test constraints follow from the native inverse and
zero flag; callers supply ordinary row cells, not polynomial evaluations. -/
theorem native_zero_test (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (gate x : Expr) (inv flag a : Nat) (enabled : Bool)
    (hg : gate.eval tr t r pub = if enabled then 1 else 0)
    (hx : x.eval tr t r pub = Fp.ofNat a)
    (hi : tr.cell t r inv = Fp.ofNat (finv a))
    (hf : tr.cell t r flag = if enabled && (a % P == 0) then 1 else 0) :
    ∀ e ∈ Codec.isZ gate x inv flag, e.eval tr t r pub = 0 := by
  intro e he
  simp only [Codec.isZ, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · change gate.eval tr t r pub * (tr.cell t r flag + -(1 + -(x.eval tr t r pub * tr.cell t r inv))) = 0
    rw [hg,hx,hi,hf]
    have h := SchedField.zero_flag a
    cases enabled <;> by_cases hz : a % P = 0 <;> simp [hz] at h ⊢ <;> grind
  · change gate.eval tr t r pub * (x.eval tr t r pub * tr.cell t r flag) = 0
    rw [hg,hx,hf]
    have h := SchedField.flag_annihilates a
    cases enabled <;> by_cases hz : a % P = 0 <;> simp [hz] at h ⊢ <;> grind
  · change (1 + -gate.eval tr t r pub) * tr.cell t r flag = 0
    rw [hg,hf]
    cases enabled <;> by_cases hz : a % P = 0 <;> simp [hz] <;> grind
end ZkFormal.NearV3.Candidates.CodecZeroTest
