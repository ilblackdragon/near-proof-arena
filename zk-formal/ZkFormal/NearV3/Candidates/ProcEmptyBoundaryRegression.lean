import ZkFormal.NearV3.Candidates.ProcKeyRotate
namespace ZkFormal.NearV3.Candidates.ProcEmptyBoundaryRegression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.Chacha.Table.E

def empty0 (R : Run) : Run := { R with tau := 0, seed := List.replicate 32 0, rounds := [] }
def empty1 (R : Run) : Run := { R with tau := 1, seed := 1 :: List.replicate 31 0, rounds := [] }

def concatenated (R : Run) : Trace Fp :=
  ⟨fun _=>22,fun _ r c=>Fp.ofNat ((if r<16 then keyV (empty0 R) r else keyV (empty1 R) (r-16)).cell c)⟩

def rotation0 : Expr := .mul (c Proc.kK) (sub (n (Proc.colL 0)) (c (Proc.colL 1)))

theorem rotation0_member : rotation0∈Proc.cKey := by
  simp only [Proc.cKey,List.mem_append]
  apply Or.inl
  apply Or.inr
  apply List.mem_map.2
  exact ⟨0,by decide,rfl⟩

/-- Two empty-round native key blocks with different first limbs fail the current
last-key rotation equation. This is not an accepted-checker reachability claim. -/
theorem boundary_value (R : Run) : rotation0.eval (concatenated R) 0 15 []=1 := by
  change (concatenated R).cell 0 15 Proc.kK *
    ((concatenated R).cell 0 (16 % (2^22)) (Proc.colL 0) +
      -(concatenated R).cell 0 15 (Proc.colL 1))=1
  rw [Nat.mod_eq_of_lt (by decide : 16<2^22)]
  simp [concatenated,PV.cell,Proc.kK,Proc.colL,keyV,empty0,empty1,keyLimb,List.getD]
  change (1 : Fp)*(1 + -0)=1
  grind

theorem first_rows (R : Run) : procVs (empty0 R)=keyVs (empty0 R) := by
  simp [procVs,empty0]
theorem second_rows (R : Run) : procVs (empty1 R)=keyVs (empty1 R) := by
  simp [procVs,empty1]
end ZkFormal.NearV3.Candidates.ProcEmptyBoundaryRegression
