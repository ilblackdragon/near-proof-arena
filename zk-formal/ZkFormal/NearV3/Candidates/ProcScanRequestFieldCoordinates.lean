import ZkFormal.NearV3.Candidates.ProcScanRequestFieldEquations
namespace ZkFormal.NearV3.Candidates.ProcScanRequestFieldCoordinates
open ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor ProcScanRequestFieldEquations
attribute [local irreducible] ProcScanRequestFactor.row

theorem next_y (R:Run)(c:CReq)(rho jj cv jn cn:Nat) :
    cell R c (rho+1) jn cn Scan.y =cell R c rho jj cv Scan.y+
      cell R c rho jj cv Scan.u0*cell R c rho jj cv Scan.u1 := by
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  have hn:=ProcScanRequestCells.progress R c (rho+1) jn cn
  simp only [cell]
  rw [hn.2.2.2.2.2.2.2,hp.2.2.2.2.2.2.2,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1,ofNat_mul',ofNat_add']
  apply congrArg Fp.ofNat
  rw [(ProcScanBitmapArithmetic.two_bits (rho%4) (Nat.mod_lt _ (by decide))).2]
  exact (ProcScanBitmapArithmetic.coordinate_next rho).1

theorem next_u (R:Run)(c:CReq)(rho jj cv jn cn:Nat) :
    cell R c (rho+1) jn cn Scan.u0+2*cell R c (rho+1) jn cn Scan.u1 =
      cell R c rho jj cv Scan.u0+2*cell R c rho jj cv Scan.u1+1-
      4*(cell R c rho jj cv Scan.u0*cell R c rho jj cv Scan.u1) := by
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  have hn:=ProcScanRequestCells.progress R c (rho+1) jn cn
  simp only [cell]
  rw [hn.2.2.2.2.2.1,hn.2.2.2.2.2.2.1,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1]
  have hb:=ProcScanBitmapArithmetic.two_bits (rho%4) (Nat.mod_lt _ (by decide))
  have hnbit:=ProcScanBitmapArithmetic.two_bits ((rho+1)%4) (Nat.mod_lt _ (by decide))
  have hc:=ProcScanBitmapArithmetic.coordinate_next rho
  have he:((rho+1)%4)+4*(bit (rho%4) 0*bit (rho%4) 1)=rho%4+1 := by
    rw [hb.2]
    have ht:=hc.2
    by_cases ht3:rho%4=3
    · simp only [ht3,b2n,beq_self_eq_true,ite_true] at ht ⊢
      omega
    · simp [b2n,ht3] at ht ⊢
      omega
  conv at he => lhs;lhs;rw [hnbit.1]
  conv at he => rhs;lhs;rw [hb.1]
  have hf:=congrArg Fp.ofNat he
  simp only [←ofNat_add',←ofNat_mul'] at hf
  clear hp hn hb hnbit hc he
  change _+Fp.ofNat 4*_= _+Fp.ofNat 1 at hf
  change Fp.ofNat _+Fp.ofNat 2*Fp.ofNat _ =
    Fp.ofNat _+Fp.ofNat 2*Fp.ofNat _+Fp.ofNat 1-Fp.ofNat 4*(Fp.ofNat _*Fp.ofNat _)
  grind
end ZkFormal.NearV3.Candidates.ProcScanRequestFieldCoordinates
