import ZkFormal.NearV3.Assembly.RcptGasFlagNativeComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.Air RcptV3
open ZkFormal.Near.Render RcptGen RcptP

def gasTokenDigits (x : TokenInput) (i : Nat) : Nat := gasByte x.before i+gasByte x.burnt i
def gasTokenCarry (x : TokenInput) : Nat→Nat := chain (gasTokenDigits x)

theorem gasTokenCarry_zero (x : TokenInput) : gasTokenCarry x 0=0 := rfl

theorem gasTokenCarry_le (x : TokenInput) (i : Nat) : gasTokenCarry x i≤1 := by
  apply chain_le (gasTokenDigits x) (M:=1) _ i
  intro j
  have h0 := gasByte_lt x.before j
  have h1 := gasByte_lt x.burnt j
  unfold gasTokenDigits
  omega

theorem gasToken_value (x : TokenInput) (h : x.before+x.burnt<256^16) :
    V (gasTokenDigits x) 16=x.before+x.burnt := by
  unfold gasTokenDigits
  rw [V_add]
  unfold gasByte
  rw [V_leBytes_of (Nat.le_refl _) (by omega : x.before<256^16),
    V_leBytes_of (Nat.le_refl _) (by omega : x.burnt<256^16)]

theorem gasTokenCarry_final (x : TokenInput) (h : x.before+x.burnt<256^16) :
    gasTokenCarry x 16=0 := by
  exact chain_zero_of _ (by rw [gasToken_value x h];exact h)

theorem gasToken_step (x : TokenInput) (h : x.before+x.burnt<256^16) (i : Nat) (hi : i<16) :
    gasByte x.before i+gasByte x.burnt i+gasTokenCarry x i=
      gasByte (x.before+x.burnt) i+256*gasTokenCarry x (i+1) := by
  have hh := chain_step (gasTokenDigits x) i
  rw [chain_digit _ (n:=16) hi,gasToken_value x h] at hh
  have hb : gasByte (x.before+x.burnt) i=(x.before+x.burnt)/256^i%256 := by
    simp only [gasByte,leBytes_getD,if_pos hi]
  rw [←hb] at hh
  exact hh

end ZkFormal.NearV3.Assembly.RcptSkeleton
