import ZkFormal.NearV3.Candidates.ProcScanRequestFieldFlags
namespace ZkFormal.NearV3.Candidates.ProcScanRequestEndFlag
open ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor ProcScanRequestFieldEquations
attribute [local irreducible] ProcScanRequestFactor.row

theorem mask (R:Run)(c:CReq)(rho jj cv:Nat) :
    cell R c rho jj cv Scan.re=cell R c rho jj cv Scan.e4*
      cell R c rho jj cv Scan.u0*cell R c rho jj cv Scan.u1 := by
  have hf:=ProcScanRequestCells.flags R c rho jj cv
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  simp only [cell,hf.2.1,hf.1,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1]
  rw [ofNat_mul',ofNat_mul']
  apply congrArg Fp.ofNat
  rw [Nat.mul_assoc,(ProcScanBitmapArithmetic.two_bits (rho%4) (Nat.mod_lt _ (by decide))).2]
  cases rho/4==4 <;> cases rho%4==3 <;> decide +kernel

theorem terminal (R:Run)(c:CReq)(rho jj cv:Nat)(hr:rho<20) :
    cell R c rho jj cv Scan.re=if rho=19 then 1 else 0 := by
  have hf:=ProcScanRequestCells.flags R c rho jj cv
  simp only [cell,hf.2.1,b2n,Bool.and_eq_true,beq_iff_eq]
  have he:(rho/4=4 ∧rho%4=3)↔rho=19:=by omega
  simp only [he]
  split <;> rfl
end ZkFormal.NearV3.Candidates.ProcScanRequestEndFlag
