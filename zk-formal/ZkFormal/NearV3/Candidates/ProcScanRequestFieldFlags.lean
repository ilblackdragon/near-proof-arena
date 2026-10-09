import ZkFormal.NearV3.Candidates.ProcScanRequestFieldEquations
namespace ZkFormal.NearV3.Candidates.ProcScanRequestFieldFlags
open NearSpecV3.Scheduler ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor ProcScanRequestFieldEquations
attribute [local irreducible] ProcScanRequestFactor.row

theorem y_test (R:Run)(c:CReq)(rho jj cv:Nat)(hr:rho<20) :
    cell R c rho jj cv Scan.e4 =1-
      (cell R c rho jj cv Scan.y-4)*cell R c rho jj cv Scan.iy := by
  have hf:=ProcScanRequestCells.flags R c rho jj cv
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  simp only [cell,hf.1,hf.2.2.1,hp.2.2.2.2.2.2.2,b2n,beq_iff_eq]
  have h:=ProcScanRequestArithmetic.y_test rho hr
  clear hf hp
  split <;> simp_all only [ite_true,ite_false]
  all_goals try simp only [show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals grind

theorem y_zero (R:Run)(c:CReq)(rho jj cv:Nat) :
    (cell R c rho jj cv Scan.y-4)*cell R c rho jj cv Scan.e4=0 := by
  have hf:=ProcScanRequestCells.flags R c rho jj cv
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  simp only [cell,hf.1,hp.2.2.2.2.2.2.2,b2n,beq_iff_eq]
  have h:=ProcScanRequestArithmetic.y_annihilate rho
  clear hf hp
  split <;> simp_all only [ite_true,ite_false]
  all_goals exact h

theorem key_test (R:Run)(c:CReq)(rho jj cv:Nat)(hk:c.key<P) :
    cell R c rho jj cv Scan.zk0=1-cell R c rho jj cv Scan.key*cell R c rho jj cv Scan.ikey := by
  have hf:=ProcScanRequestCells.flags R c rho jj cv
  have hp:=ProcScanRequestCells.payload R c rho jj cv
  simp only [cell,hf.2.2.2.2,hf.2.2.2.1,hp.2.2.2.1,b2n,beq_iff_eq]
  have h:=ProcScanRequestArithmetic.key_test c.key hk
  clear hf hp
  split <;> simp_all only [ite_true,ite_false]
  all_goals try simp only [show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals grind

theorem key_zero (R:Run)(c:CReq)(rho jj cv:Nat) :
    cell R c rho jj cv Scan.key*cell R c rho jj cv Scan.zk0=0 := by
  have hf:=ProcScanRequestCells.flags R c rho jj cv
  have hp:=ProcScanRequestCells.payload R c rho jj cv
  simp only [cell,hf.2.2.2.2,hp.2.2.2.1,b2n,beq_iff_eq]
  have h:=ProcScanRequestArithmetic.key_annihilate c.key
  clear hf hp
  split <;> simp_all only [ite_true,ite_false]
  all_goals exact h
end ZkFormal.NearV3.Candidates.ProcScanRequestFieldFlags
