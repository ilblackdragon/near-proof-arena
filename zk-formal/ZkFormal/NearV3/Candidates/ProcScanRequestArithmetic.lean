import ZkFormal.NearV3.Candidates.ProcScanRequestFactor
import ZkFormal.NearV3.Candidates.ProcPriorCodecGridField
namespace ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor

theorem position (rho:Nat) : pos rho=2*rho := by
  have h:=Nat.mod_add_div rho 4
  unfold pos
  omega

theorem coordinate_bounds (rho:Nat)(h:rho<20) : rho/4≤4 ∧rho%4<4 ∧pos rho+2≤40 := by
  rw [position]
  omega

theorem quotient_bound (D rho k:Nat)(hd:D≤4194304)(hr:rho<20)(hk:k≤2) :
    D*(pos rho+k)/40<2^23 := by
  have hc:=coordinate_bounds rho hr
  have hm:=Nat.mul_le_mul_left D (show pos rho+k≤40 by omega)
  have hdiv:=Nat.div_le_div_right hm (c:=40)
  rw [Nat.mul_div_cancel D (by decide : 0<40)] at hdiv
  omega

theorem native_D (I:Input)(tau:Nat)(R:Run)(hr:ActualRun.run I tau=.ok R)
    (hp:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p) :
    R.D≤4194304 := by
  have hf:=ProcActualRunProjection.run_fields I tau R hr
  have hparam:=ZkFormal.NearV3.Sched.pv86_base_le hp
  rw [hf.2.2.2.1,hparam.2]
  omega

theorem remainder_bounds (x:Nat) : x%40<64 ∧ bit (x%40) 5*bit (x%40) 4=0 ∧
    bit (x%40) 5*bit (x%40) 3=0 := by
  have hx:=Nat.mod_lt x (by decide : 0<40)
  unfold bit
  simp only [Nat.reducePow]
  have hsmall:x%40/32≤1:=by omega
  by_cases h:x%40<32
  · have hz:x%40/32=0:=by omega
    simp [hz];omega
  · have h4:x%40/16%2=0:=by omega
    have h3:x%40/8%2=0:=by omega
    simp [h4,h3];omega

theorem quotient_remainder (D rho k:Nat) :
    40*(D*(pos rho+k)/40)+D*(pos rho+k)%40=D*(pos rho+k) := by
  omega

theorem y_test (rho:Nat)(hr:rho<20) :
    (Fp.ofNat (rho/4)-4)*Fp.ofNat (if rho/4=4 then 0 else finv (fsub (rho/4) 4))=
      1-(if rho/4=4 then 1 else 0) := by
  have hb:rho/4<P:=by unfold P;omega
  by_cases h:rho/4=4
  · simp only [h,ite_true]
    change ((4:Fp)-4)*0=1-1
    grind
  · rw [if_neg h,if_neg h]
    have hz:=ProcKeyInverse.difference_zero (rho/4) 4 hb (by decide)
    change (Fp.ofNat (rho/4)-Fp.ofNat 4)*_=1-0
    rw [←SchedField.fsub_cast,SchedField.inverse_product,if_neg (fun e=>h (hz.mp e))]
    grind

theorem y_annihilate (rho:Nat) :
    (Fp.ofNat (rho/4)-4)*(if rho/4=4 then 1 else 0)=0 := by
  split
  · rename_i h;rw [h];change ((4:Fp)-4)*1=0;grind
  · grind

theorem key_test (key:Nat)(hk:key<P) :
    Fp.ofNat key*Fp.ofNat (finv key)=1-(if key=0 then 1 else 0) := by
  rw [SchedField.inverse_product,Nat.mod_eq_of_lt hk]
  split <;> grind

theorem key_annihilate (key:Nat) : Fp.ofNat key*(if key=0 then 1 else 0)=0 := by
  split
  · rename_i h;rw [h];change (0:Fp)*1=0;grind
  · grind
end ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic
