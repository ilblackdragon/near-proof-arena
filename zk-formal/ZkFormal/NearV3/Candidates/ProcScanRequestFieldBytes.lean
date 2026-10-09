import ZkFormal.NearV3.Candidates.ProcScanRequestFieldEquations
import ZkFormal.NearV3.Candidates.ProcScanRequestRegisters
namespace ZkFormal.NearV3.Candidates.ProcScanRequestFieldBytes
open NearSpecV3.Scheduler ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor ProcScanRequestFieldEquations
attribute [local irreducible] ProcScanRequestFactor.row

theorem exhausted (R:Run)(c:CReq)(rho jj cv:Nat)(hu:rho%4=3) :
    cell R c rho jj cv (Scan.q 0)=cell R c rho jj cv Scan.b0+2*cell R c rho jj cv Scan.b1 := by
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  simp only [cell]
  rw [ProcScanRequestRegisters.cell R c rho jj cv 0 (by decide),hp.2.2.2.1,hp.2.2.2.2.1]
  change _=Fp.ofNat _+Fp.ofNat 2*Fp.ofNat _
  rw [ofNat_mul',ofNat_add']
  apply congrArg Fp.ofNat
  simpa only [ProcScanRequestArithmetic.position] using ProcScanByteTransition.exhausted c.bm rho hu

theorem consumes (R:Run)(c:CReq)(rho jj cv jn cn:Nat)(hu:rho%4≠3) :
    cell R c rho jj cv (Scan.q 0)=cell R c rho jj cv Scan.b0+2*cell R c rho jj cv Scan.b1+
      4*cell R c (rho+1) jn cn (Scan.q 0) := by
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  simp only [cell]
  rw [ProcScanRequestRegisters.cell R c rho jj cv 0 (by decide),
    ProcScanRequestRegisters.cell R c (rho+1) jn cn 0 (by decide),hp.2.2.2.1,hp.2.2.2.2.1]
  change _=Fp.ofNat _+Fp.ofNat 2*Fp.ofNat _+Fp.ofNat 4*Fp.ofNat _
  rw [ofNat_mul',ofNat_add',ofNat_mul',ofNat_add']
  apply congrArg Fp.ofNat
  simpa only [ProcScanRequestArithmetic.position] using ProcScanByteTransition.consumes c.bm rho hu

theorem rotates (R:Run)(c:CReq)(rho jj cv jn cn i:Nat)(hi:i<4)(hu:rho%4=3) :
    cell R c (rho+1) jn cn (Scan.q i)=cell R c rho jj cv (Scan.q (i+1)) :=
  congrArg Fp.ofNat (ProcScanRequestRegisters.rotates R c rho jj cv jn cn i hi hu)

theorem stays (R:Run)(c:CReq)(rho jj cv jn cn i:Nat)(hi:i<4)(hu:rho%4≠3) :
    cell R c (rho+1) jn cn (Scan.q (i+1))=cell R c rho jj cv (Scan.q (i+1)) :=
  congrArg Fp.ofNat (ProcScanRequestRegisters.stays R c rho jj cv jn cn (i+1) (by omega) hu)
end ZkFormal.NearV3.Candidates.ProcScanRequestFieldBytes
