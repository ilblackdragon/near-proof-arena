import ZkFormal.NearV3.Candidates.ProcScanRequestRangePhysical
import ZkFormal.NearV3.Candidates.ProcScanRequestFieldEquations
namespace ZkFormal.NearV3.Candidates.ProcScanRequestFieldDivision
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row

theorem remainders (R:Run)(c:CReq)(rho jj cv:Nat)(tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!) :
    Scan.r0E.eval tr t r pub=Fp.ofNat (R.D*(pos rho+1)%40) ∧
    Scan.r1E.eval tr t r pub=Fp.ofNat (R.D*(pos rho+2)%40) := by
  have hrb:=ProcScanRequestBitCells.remainders R c rho jj cv
  have hb (x i:Nat):bit x i<P:=by have h:=Complete.bit_le x i;unfold P;omega
  have h0:=ProcScanRequestRange.num_bits (tenv tr t r pub) Scan.rb0 6 (R.D*(pos rho+1)%40)
    (by have h:=Nat.mod_lt (R.D*(pos rho+1)) (by decide : 0<40);omega) (fun i hi=>by
      change (tr.cell t r (Scan.rb0 i)).toNat=_
      rw [hrow,(hrb i hi).1,Fp.toNat_ofNat,Nat.mod_eq_of_lt (hb _ _)])
  have h1:=ProcScanRequestRange.num_bits (tenv tr t r pub) Scan.rb1 6 (R.D*(pos rho+2)%40)
    (by have h:=Nat.mod_lt (R.D*(pos rho+2)) (by decide : 0<40);omega) (fun i hi=>by
      change (tr.cell t r (Scan.rb1 i)).toNat=_
      rw [hrow,(hrb i hi).2,Fp.toNat_ofNat,Nat.mod_eq_of_lt (hb _ _)])
  constructor
  · rw [Scan.r0E,eval_eq,h0]
    exact ZkFormal.Chacha.intCast_ofNat _
  · rw [Scan.r1E,eval_eq,h1]
    exact ZkFormal.Chacha.intCast_ofNat _

theorem position (R:Run)(c:CReq)(rho jj cv:Nat)(tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!) :
    Scan.posE.eval tr t r pub=Fp.ofNat (pos rho) := by
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  change (8:Fp)*tr.cell t r Scan.y+2*(tr.cell t r Scan.u0+2*tr.cell t r Scan.u1)=_
  rw [hrow,hrow,hrow,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1,hp.2.2.2.2.2.2.2]
  change Fp.ofNat 8*Fp.ofNat _+Fp.ofNat 2*(Fp.ofNat _+Fp.ofNat 2*Fp.ofNat _)=_
  rw [ofNat_mul',ofNat_mul',ofNat_add',ofNat_mul',ofNat_add']
  apply congrArg Fp.ofNat
  rw [←(ProcScanBitmapArithmetic.two_bits (rho%4) (Nat.mod_lt _ (by decide))).1]
  rfl
theorem divisions (R:Run)(c:CReq)(rho jj cv:Nat)(tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!) :
    40*tr.cell t r Scan.Q0+Scan.r0E.eval tr t r pub=
      tr.cell t r Scan.dd*(Scan.posE.eval tr t r pub+1) ∧
    40*tr.cell t r Scan.Q1+Scan.r1E.eval tr t r pub=
      tr.cell t r Scan.dd*(Scan.posE.eval tr t r pub+2) := by
  have hr:=remainders R c rho jj cv tr t r pub hrow
  have hp:=position R c rho jj cv tr t r pub hrow
  have hq:=ProcScanRequestCells.quotients R c rho jj cv
  have hc:=ProcScanRequestCells.controls R c rho jj cv
  rw [hr.1,hr.2,hp,hrow,hrow,hrow,hq.1,hq.2.1,hc.2.2.2.2.2.2.1]
  constructor
  · change Fp.ofNat 40*Fp.ofNat _+Fp.ofNat _=Fp.ofNat _*(Fp.ofNat _+Fp.ofNat 1)
    rw [ofNat_mul',ofNat_add',ofNat_add',ofNat_mul']
    exact congrArg Fp.ofNat (ProcScanRequestArithmetic.quotient_remainder R.D rho 1)
  · change Fp.ofNat 40*Fp.ofNat _+Fp.ofNat _=Fp.ofNat _*(Fp.ofNat _+Fp.ofNat 2)
    rw [ofNat_mul',ofNat_add',ofNat_add',ofNat_mul']
    exact congrArg Fp.ofNat (ProcScanRequestArithmetic.quotient_remainder R.D rho 2)

theorem remainder_high_bits (R:Run)(c:CReq)(rho jj cv:Nat)(tr:Trace Fp)(t r:Nat)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!) :
    tr.cell t r (Scan.rb0 5)*tr.cell t r (Scan.rb0 4)=0 ∧
    tr.cell t r (Scan.rb0 5)*tr.cell t r (Scan.rb0 3)=0 ∧
    tr.cell t r (Scan.rb1 5)*tr.cell t r (Scan.rb1 4)=0 ∧
    tr.cell t r (Scan.rb1 5)*tr.cell t r (Scan.rb1 3)=0 := by
  have h5:=ProcScanRequestBitCells.remainders R c rho jj cv 5 (by decide)
  have h4:=ProcScanRequestBitCells.remainders R c rho jj cv 4 (by decide)
  have h3:=ProcScanRequestBitCells.remainders R c rho jj cv 3 (by decide)
  have ha:=ProcScanRequestArithmetic.remainder_bounds (R.D*(pos rho+1))
  have hb:=ProcScanRequestArithmetic.remainder_bounds (R.D*(pos rho+2))
  simp only [hrow,h5.1,h5.2,h4.1,h4.2,h3.1,h3.2,ofNat_mul',ha.2.1,ha.2.2,hb.2.1,hb.2.2]
  decide

end ZkFormal.NearV3.Candidates.ProcScanRequestFieldDivision
