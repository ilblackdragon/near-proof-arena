import ZkFormal.NearV3.Candidates.ProcScanRequestBitCells
namespace ZkFormal.NearV3.Candidates.ProcScanRequestRange
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

theorem num_bits (Z:ZEnv)(cols:Nat→Nat)(n x:Nat)(hx:x<2^n)
    (h:∀i,i<n→Z.cur (cols i)=bit x i) :
    zev Z (ZkFormal.Chacha.Rng.Table.num cols n)=Int.ofNat x := by
  unfold ZkFormal.Chacha.Rng.Table.num
  rw [zev_sum_pow Z _ (bt x) n (by
    intro i hi
    change (Z.cur (cols i):Int)=_
    rw [h i hi]
    rfl),nbits_bt,Nat.mod_eq_of_lt hx]
  rfl

attribute [local irreducible] ProcScanRequestFactor.row

theorem range (R:Run)(c:CReq)(rho jj cv:Nat)(hr:rho<20)(hd:R.D≤4194304)(Z:ZEnv)
    (hrow:∀col,Z.cur col=(row R c rho jj cv)[col]!) :
    ∀e∈Dist.cRange,zev Z e=0 := by
  have hq:=ProcScanRequestCells.quotients R c rho jj cv
  have hqb:=ProcScanRequestBitCells.quotients R c rho jj cv
  have hrb:=ProcScanRequestBitCells.remainders R c rho jj cv
  have h0:=num_bits Z Scan.qb0 23 (R.D*(pos rho+1)/40)
    (ProcScanRequestArithmetic.quotient_bound _ _ _ hd hr (by decide))
    (fun i hi=>by rw [hrow,(hqb i hi).1])
  have h1:=num_bits Z Scan.qb1 23 (R.D*(pos rho+2)/40)
    (ProcScanRequestArithmetic.quotient_bound _ _ _ hd hr (by decide))
    (fun i hi=>by rw [hrow,(hqb i hi).2])
  have h2:=num_bits Z Scan.rb0 6 (R.D*(pos rho+1)%40)
    (by have h:=Nat.mod_lt (R.D*(pos rho+1)) (by decide : 0<40);omega)
    (fun i hi=>by rw [hrow,(hrb i hi).1])
  have h3:=num_bits Z Scan.rb1 6 (R.D*(pos rho+2)%40)
    (by have h:=Nat.mod_lt (R.D*(pos rho+2)) (by decide : 0<40);omega)
    (fun i hi=>by rw [hrow,(hrb i hi).2])
  unfold Scan.qb0 at h0
  unfold Scan.qb1 at h1
  unfold Scan.rb0 at h2
  unfold Scan.rb1 at h3
  simp only [Scan.Q0,Scan.Q1] at hq
  simp only [Dist.cRange,List.forall_mem_cons,List.forall_mem_nil,zev_sub,zev_c]
  refine ⟨?_,?_,?_,?_,by simp⟩
  · rw [h0,hrow,hq.1];simp
  · rw [h1,hrow,hq.2.1];simp
  · rw [h2,hrow,hq.2.2.1];simp
  · rw [h3,hrow,hq.2.2.2];simp

end ZkFormal.NearV3.Candidates.ProcScanRequestRange
