import ZkFormal.NearV3.Render.Ups.MemScalarBounds
import ZkFormal.NearV3.Render.Ups.MemBounds

/-! Wide carries accommodate complete scalar inputs, including long prefix constants. -/
namespace ZkFormal.NearV3.Render.UpsGen

theorem coV_widebounds (I : UpsInst) (Q : UpsPartI)
    (hx : ∀ i,i<7 → -(2^23+1024)≤sigV Q*X1V I Q i ∧ sigV Q*X1V I Q i≤2^23+1024) :
    ∀ i,i<7 → -65536≤coV I Q i ∧ coV I Q i≤65535 := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hc := inside_carry I Q (i:=0) (by omega)
    have hb := tV_bounds I Q 0
    have hx := hx 0 hi
    simp only [ite_true] at hc
    omega
  | succ i ih =>
    intro hi
    have hc := inside_carry I Q (i:=i+1) (by omega)
    have hb := tV_bounds I Q (i+1)
    have hx := hx (i+1) hi
    have hp := ih (by omega)
    simp only [Nat.add_sub_cancel,show i+1≠0 by omega,ite_false] at hc
    omega

theorem co2V_widebounds (I : UpsInst) (Q : UpsPartI) (hn : Q.neg≤1)
    (he : ∀ i,i<8 → 0≤EinV I Q i ∧ EinV I Q i≤2^23+1024) :
    ∀ i,i<8 → 0≤co2V I Q i ∧ co2V I Q i<65536 := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hc := outside_carry I Q hn (i:=0) (by omega)
    have hb := tV_bounds I Q 0
    have he := he 0 hi
    rcases (show Q.neg=0 ∨ Q.neg=1 by omega) with h|h <;>
      simp only [h,Int.natCast_zero,Int.natCast_one,Int.sub_zero,Int.sub_self,
        Int.one_mul,Int.zero_mul,ite_true] at hc <;> omega
  | succ i ih =>
    intro hi
    have hc := outside_carry I Q hn (i:=i+1) (by omega)
    have hb := tV_bounds I Q (i+1)
    have he := he (i+1) hi
    have hp := ih (by omega)
    rcases (show Q.neg=0 ∨ Q.neg=1 by omega) with h|h <;>
      simp only [h,Int.natCast_zero,Int.natCast_one,Int.sub_zero,Int.sub_self,
        Int.one_mul,Int.zero_mul,Nat.add_sub_cancel,show i+1≠0 by omega,ite_false] at hc <;> omega

theorem encoded_inside_widebounds (I : UpsInst) (Q : UpsPartI)
    (hx : ∀ i,i<7 → -(2^23+1024)≤sigV Q*X1V I Q i ∧ sigV Q*X1V I Q i≤2^23+1024)
    (ht : 0≤TV I Q ∧ TV I Q<131072*256^8) :
    ∀ i,i<8 → 0≤coV I Q i+(if i<7 then 65536 else 0) ∧
      coV I Q i+(if i<7 then 65536 else 0)<131072 := by
  intro i hi
  by_cases hl : i<7
  · have hc := coV_widebounds I Q hx i hl
    simp only [hl,ite_true]
    omega
  · have hi7 : i=7 := by omega
    subst i
    simp only [Nat.lt_irrefl,ite_false,Int.add_zero,inside_last_high]
    simp only [Int.reducePow,Int.reduceMul] at ht ⊢
    omega
end ZkFormal.NearV3.Render.UpsGen
