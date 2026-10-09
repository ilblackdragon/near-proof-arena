import ZkFormal.NearV3.Candidates.ProcScanRequestRange
namespace ZkFormal.NearV3.Candidates.ProcScanRequestRangePhysical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row

private theorem bit_small (x i:Nat) : bit x i<P := by
  have h:=Complete.bit_le x i
  unfold P;omega

theorem physical (R:Run)(c:CReq)(rho jj cv:Nat)(hr:rho<20)(hd:R.D≤4194304)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!) :
    ∀e∈Dist.cRange,e.eval tr t r pub=0 := by
  have hq:=ProcScanRequestCells.quotients R c rho jj cv
  have hqb:=ProcScanRequestBitCells.quotients R c rho jj cv
  have hrb:=ProcScanRequestBitCells.remainders R c rho jj cv
  have h0:=ProcScanRequestRange.num_bits (tenv tr t r pub) Scan.qb0 23 (R.D*(pos rho+1)/40)
    (ProcScanRequestArithmetic.quotient_bound _ _ _ hd hr (by decide)) (fun i hi=>by
      change (tr.cell t r (Scan.qb0 i)).toNat=_
      rw [hrow,(hqb i hi).1,Fp.toNat_ofNat,Nat.mod_eq_of_lt (bit_small _ _)])
  have h1:=ProcScanRequestRange.num_bits (tenv tr t r pub) Scan.qb1 23 (R.D*(pos rho+2)/40)
    (ProcScanRequestArithmetic.quotient_bound _ _ _ hd hr (by decide)) (fun i hi=>by
      change (tr.cell t r (Scan.qb1 i)).toNat=_
      rw [hrow,(hqb i hi).2,Fp.toNat_ofNat,Nat.mod_eq_of_lt (bit_small _ _)])
  have h2:=ProcScanRequestRange.num_bits (tenv tr t r pub) Scan.rb0 6 (R.D*(pos rho+1)%40)
    (by have h:=Nat.mod_lt (R.D*(pos rho+1)) (by decide : 0<40);omega) (fun i hi=>by
      change (tr.cell t r (Scan.rb0 i)).toNat=_
      rw [hrow,(hrb i hi).1,Fp.toNat_ofNat,Nat.mod_eq_of_lt (bit_small _ _)])
  have h3:=ProcScanRequestRange.num_bits (tenv tr t r pub) Scan.rb1 6 (R.D*(pos rho+2)%40)
    (by have h:=Nat.mod_lt (R.D*(pos rho+2)) (by decide : 0<40);omega) (fun i hi=>by
      change (tr.cell t r (Scan.rb1 i)).toNat=_
      rw [hrow,(hrb i hi).2,Fp.toNat_ofNat,Nat.mod_eq_of_lt (bit_small _ _)])
  unfold Scan.qb0 at h0
  unfold Scan.qb1 at h1
  unfold Scan.rb0 at h2
  unfold Scan.rb1 at h3
  simp only [Scan.Q0,Scan.Q1] at hq
  have hv0:(tenv tr t r pub).cur Dist.q1=R.D*(pos rho+1)/40 := by
    change (tr.cell t r Dist.q1).toNat=_
    rw [hrow,hq.1,Fp.toNat_ofNat,Nat.mod_eq_of_lt]
    have h:=ProcScanRequestArithmetic.quotient_bound R.D rho 1 hd hr (by decide)
    unfold P;omega
  have hv1:(tenv tr t r pub).cur Dist.q2=R.D*(pos rho+2)/40 := by
    change (tr.cell t r Dist.q2).toNat=_
    rw [hrow,hq.2.1,Fp.toNat_ofNat,Nat.mod_eq_of_lt]
    have h:=ProcScanRequestArithmetic.quotient_bound R.D rho 2 hd hr (by decide)
    unfold P;omega
  have hv2:(tenv tr t r pub).cur Dist.r1=R.D*(pos rho+1)%40 := by
    change (tr.cell t r Dist.r1).toNat=_
    rw [hrow,hq.2.2.1,Fp.toNat_ofNat,Nat.mod_eq_of_lt]
    have h:=Nat.mod_lt (R.D*(pos rho+1)) (by decide : 0<40)
    unfold P;omega
  have hv3:(tenv tr t r pub).cur Dist.r2=R.D*(pos rho+2)%40 := by
    change (tr.cell t r Dist.r2).toNat=_
    rw [hrow,hq.2.2.2,Fp.toNat_ofNat,Nat.mod_eq_of_lt]
    have h:=Nat.mod_lt (R.D*(pos rho+2)) (by decide : 0<40)
    unfold P;omega
  intro e he
  apply eval_zero_of
  simp only [Dist.cRange,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl
  all_goals simp only [zev_sub,zev_c,h0,h1,h2,h3,hv0,hv1,hv2,hv3];simp
end ZkFormal.NearV3.Candidates.ProcScanRequestRangePhysical
