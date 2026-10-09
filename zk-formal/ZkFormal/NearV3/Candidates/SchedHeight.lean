import ZkFormal.NearV3.Sched.Complete.Cmp
namespace ZkFormal.NearV3.Candidates.SchedHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched.Complete
/-- Generate native rows directly at the shared physical clock. -/
def trace (rows : Array (Array Nat)) (pad : Nat → Array Nat) : Trace Fp :=
  ⟨fun _=>22, fun _ r c=>Fp.ofNat (natCell rows pad r c)⟩
theorem env (rows : Array (Array Nat)) (pad : Nat → Array Nat)
    (hs : HSmall rows pad) (t r : Nat) (pub : List Fp) :
    (∀ c, (tenv (trace rows pad) t r pub).cur c = natCell rows pad r c) ∧
    (∀ c, (tenv (trace rows pad) t r pub).nxt c = natCell rows pad ((r+1) % (trace rows pad).height t) c) := by
  constructor <;> intro c <;> change (Fp.ofNat _).toNat = _ <;>
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (hs _ _)]
end ZkFormal.NearV3.Candidates.SchedHeight
