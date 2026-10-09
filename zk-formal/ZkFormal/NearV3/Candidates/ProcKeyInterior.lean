import ZkFormal.NearV3.Candidates.ProcKeyScalar
import ZkFormal.NearV3.Candidates.ProcKeyTests
namespace ZkFormal.NearV3.Candidates.ProcKeyInterior
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight ProcKeyRows
open ZkFormal.Chacha.Table.E

def rotations : List Expr := (List.range 16).map fun i=>
  .mul (c Proc.kK) (sub (n (Proc.colL i)) (c (Proc.colL ((i+1)%16))))
def carries : List Expr := (List.range 16).map fun i=>
  Proc.mul3 (.add (c Proc.kH) (c Proc.kE)) (Proc.notE (n Proc.kK))
    (sub (n (Proc.colL i)) (c (Proc.colL i)))
theorem partition : Proc.cKey=Proc.cKey.take 3++(Proc.cKey.drop 3).take 3++
    (Proc.cKey.drop 6).take 7++rotations++carries := rfl

theorem carry_zero (tr : Trace Fp) (t r i : Nat) (pub : List Fp)
    (hh : tr.cell t r Proc.kH=0) (he : tr.cell t r Proc.kE=0) :
    (Proc.mul3 (.add (c Proc.kH) (c Proc.kE)) (Proc.notE (n Proc.kK))
      (sub (n (Proc.colL i)) (c (Proc.colL i)))).eval tr t r pub=0 := by
  change ((tr.cell t r Proc.kH+tr.cell t r Proc.kE)*(1 + -tr.cell t ((r+1)%tr.height t) Proc.kK))*
    (tr.cell t ((r+1)%tr.height t) (Proc.colL i) + -tr.cell t r (Proc.colL i))=0
  rw [hh,he]
  grind

/-- Every key constraint holds at each of the first fifteen native key rows. -/
theorem key_interior (R : Run) (t k : Nat) (pub : List Fp) (hk : k<15) :
    ∀ e ∈ Proc.cKey, e.eval (trace R) t k pub=0 := by
  rw [partition]
  simp only [List.forall_mem_append]
  refine ⟨⟨⟨⟨ProcKeyTests.key_test R t k pub (by omega),
    ProcKeyStep.inside_native R t k pub hk⟩,ProcKeyScalar.scalar_native R t k pub hk⟩,?_⟩,?_⟩
  · intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 he
    exact ProcKeyRotate.rotate_native R t k pub hk i (List.mem_range.1 hi)
  · intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 he
    apply carry_zero
    · exact key_cell R t k Proc.kH (by omega)
    · exact key_cell R t k Proc.kE (by omega)
end ZkFormal.NearV3.Candidates.ProcKeyInterior
