import ZkFormal.NearV3.Assembly.RcptGasTokenNativeComplete
import ZkFormal.Near.Render.Proof.RcptGas3

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.Air RcptV3
open ZkFormal.Near.Render RcptGen RcptP

def gasMulDigits (v : Nat) : Nat→Nat := RcptGen.conv (Rcpt.G_LE.take 5) (gasByte v)
def gasMulCarry (v : Nat) : Nat→Nat := chain (gasMulDigits v)

theorem gasMul_small (v : Nat) (hv : Params.G*v<256^16) : v<256^12 := by
  rw [show Params.G=223182562500 from rfl] at hv
  simp only [Nat.reducePow] at hv ⊢
  omega

theorem gasMul_prefix (v n : Nat) (hv : Params.G*v<256^16) (hn : 12≤n) (hn' : n≤16) :
    V (gasByte v) n=v := by
  unfold gasByte
  rw [V_leBytes,Nat.min_eq_left hn',Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le (gasMul_small v hv) (Nat.pow_le_pow_right (by decide) hn)

theorem gasMul_value (v : Nat) (hv : Params.G*v<256^16) :
    V (gasMulDigits v) 16=Params.G*v := by
  unfold gasMulDigits
  rw [V_convG]
  rw [gasMul_prefix v 16 hv (by decide) (by decide),
    gasMul_prefix v 15 hv (by decide) (by decide),
    gasMul_prefix v 14 hv (by decide) (by decide),
    gasMul_prefix v 13 hv (by decide) (by decide),
    gasMul_prefix v 12 hv (by decide) (by decide)]
  rw [show Params.G=223182562500 from rfl]
  omega

theorem gasMulCarry_zero (v : Nat) : gasMulCarry v 0=0 := rfl

theorem gasMulCarry_le (v i : Nat) : gasMulCarry v i≤840 := by
  apply chain_le (gasMulDigits v) (M:=840) _ i
  intro j
  have hh := convG_le (gasByte v) (fun i=>Nat.le_of_lt_succ (gasByte_lt v i)) j
  change gasMulDigits v j≤214200 at hh
  omega

theorem gasMulCarry_final (v : Nat) (hv : Params.G*v<256^16) : gasMulCarry v 16=0 := by
  exact chain_zero_of _ (by rw [gasMul_value v hv];exact hv)

theorem gasMul_step (v : Nat) (hv : Params.G*v<256^16) (i : Nat) (hi : i<16) :
    gasMulDigits v i+gasMulCarry v i=gasByte (Params.G*v) i+256*gasMulCarry v (i+1) := by
  have hh := chain_step (gasMulDigits v) i
  rw [chain_byte _ hi (gasMul_value v hv)] at hh
  exact hh

theorem gasMul_top_zero (v : Nat) (hv : Params.G*v<256^16) (i : Nat) (hi : 12≤i) :
    gasByte v i=0 := by
  have hs := gasMul_small v hv
  unfold gasByte
  rw [leBytes_getD]
  split
  · have hb : v<256^i := Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) hi)
    rw [Nat.div_eq_of_lt hb]
  · rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
