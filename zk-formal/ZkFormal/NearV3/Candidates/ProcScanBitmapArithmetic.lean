import ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic
namespace ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor

theorem b2n_mod2 (x:Nat) : b2n (x%2==1)=x%2 := by
  unfold b2n
  have hm:=Nat.mod_lt x (by decide : 0<2)
  by_cases h:x%2=1
  · simp [h]
  · simp [h];omega

theorem getBit_eq (bm:List UInt8)(y u k:Nat)(hu:u<4)(hk:k≤1) :
    b2n (getBit bm (8*y+2*u+k))=bit ((bm.getD y 0).toNat) (2*u+k) := by
  have hd:(8*y+2*u+k)/8=y:=by omega
  have hm:(8*y+2*u+k)%8=2*u+k:=by omega
  unfold getBit bit
  rw [hd,hm,Nat.shiftRight_eq_div_pow,b2n_mod2]

theorem byte_pair (x u:Nat)(hx:x<256)(hu:u<4) :
    x/4^u=bit x (2*u)+2*bit x (2*u+1)+4*(if u=3 then 0 else x/4^(u+1)) := by
  have hcases:u=0 ∨u=1 ∨u=2 ∨u=3:=by omega
  rcases hcases with rfl|rfl|rfl|rfl <;>
    simp only [bit,Nat.reducePow,Nat.reduceAdd,Nat.reduceMul,Nat.div_one,ite_true,ite_false,Nat.reduceEqDiff] <;> omega

theorem two_bits (u:Nat)(hu:u<4) : u=bit u 0+2*bit u 1 ∧
    bit u 0*bit u 1=b2n (u==3) := by
  have hcases:u=0 ∨u=1 ∨u=2 ∨u=3:=by omega
  rcases hcases with rfl|rfl|rfl|rfl <;> decide +kernel

theorem coordinate_next (rho:Nat) :
    (rho+1)/4=rho/4+b2n (rho%4==3) ∧
    (rho+1)%4=rho%4+1-4*b2n (rho%4==3) := by
  have hm:=Nat.mod_lt rho (by decide : 0<4)
  have hd:=Nat.mod_add_div rho 4
  unfold b2n
  by_cases h:rho%4=3
  · simp [h];omega
  · simp [h];omega

theorem byte_bound (bm:List UInt8)(y:Nat) : (bm.getD y 0).toNat<256 := by
  exact UInt8.toNat_lt _

theorem native_pair (bm:List UInt8)(rho:Nat) :
    (bm.getD (rho/4) 0).toNat/4^(rho%4)=
      b2n (getBit bm (pos rho))+2*b2n (getBit bm (pos rho+1))+
        4*(if rho%4=3 then 0 else (bm.getD (rho/4) 0).toNat/4^(rho%4+1)) := by
  have hu:=Nat.mod_lt rho (by decide : 0<4)
  have h0:=getBit_eq bm (rho/4) (rho%4) 0 hu (by decide)
  have h1:=getBit_eq bm (rho/4) (rho%4) 1 hu (by decide)
  simp only [Nat.add_zero] at h0
  unfold pos
  rw [h0,h1]
  exact byte_pair _ _ (byte_bound bm _) hu
end ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic
