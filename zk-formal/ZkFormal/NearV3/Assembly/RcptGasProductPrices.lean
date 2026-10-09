import ZkFormal.NearV3.Assembly.RcptGasProductArithmetic
import ZkFormal.NearV3.Assembly.RcptNativeSurplus

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.Air RcptV3
open ZkFormal.Near.Render RcptGen RcptP

def gasBurnPrice (ctx : ApplyCtx) (r : Receipt) : Nat :=
  if r.predecessorId==AccountId.system then 0 else min r.gasPrice ctx.gasPrice

def gasSurplusPrice (ctx : ApplyCtx) (r : Receipt) : Nat :=
  if r.predecessorId==AccountId.system then 0 else r.gasPrice-min r.gasPrice ctx.gasPrice

theorem nativeBurn_price (ctx : ApplyCtx) (r : Receipt) : nativeBurn ctx r=Params.G*gasBurnPrice ctx r := by
  unfold nativeBurn gasBurnPrice
  split <;> simp_all

theorem nativeRefundAmount_price (ctx : ApplyCtx) (r : Receipt) :
    nativeRefundAmount ctx r=Params.G*gasSurplusPrice ctx r := by
  unfold nativeRefundAmount gasSurplusPrice nativeSurplus
  split <;> simp_all

theorem gasEffectiveByte_price (ctx : ApplyCtx) (r : Receipt) (i : Nat) :
    gasEffectiveByte ctx r i=gasByte (gasBurnPrice ctx r) i := by
  unfold gasEffectiveByte gasBurnPrice
  split
  · simp only [Nat.sub_self,gasByte,leBytes_getD,Nat.zero_div,Nat.zero_mod,ite_self]
  · rfl

theorem gasRawSurplusByte_price (ctx : ApplyCtx) (r : Receipt)
    (hr : r.gasPrice<256^16) (hc : ctx.gasPrice<256^16) (i : Nat) (hi : i<16) :
    gasRawSurplusByte ctx r i=gasByte (r.gasPrice-min r.gasPrice ctx.gasPrice) i := by
  unfold gasRawSurplusByte
  by_cases hge : ctx.gasPrice≤r.gasPrice
  · rw [if_pos hge,Nat.min_eq_right hge]
    have hva : V (gasByte r.gasPrice) 16=r.gasPrice := V_leBytes_of (Nat.le_refl _) hr
    have hvb : V (gasByte ctx.gasPrice) 16=ctx.gasPrice := V_leBytes_of (Nat.le_refl _) hc
    have hv := V_bdig (gasByte r.gasPrice) (gasByte ctx.gasPrice) 0
      (gasByte_lt _) (gasByte_lt _) (by decide) (n:=16) (by rw [hva,hvb];omega)
    rw [hva,hvb,Nat.sub_zero] at hv
    change V (gasDifference ctx r) 16=r.gasPrice-ctx.gasPrice at hv
    rw [gasByte,leBytes_getD,if_pos hi,←hv]
    exact (V_digit _ (gasDifference_lt ctx r) hi).symm
  · rw [if_neg hge,Nat.min_eq_left (by omega)]
    simp only [Nat.sub_self,gasByte,leBytes_getD,Nat.zero_div,Nat.zero_mod,ite_self]

theorem gasNativeSurplusByte_price (ctx : ApplyCtx) (r : Receipt)
    (hr : r.gasPrice<256^16) (hc : ctx.gasPrice<256^16) (i : Nat) (hi : i<16) :
    gasNativeSurplusByte ctx r i=gasByte (gasSurplusPrice ctx r) i := by
  unfold gasNativeSurplusByte gasSurplusPrice
  split
  · simp only [Nat.sub_self,gasByte,leBytes_getD,Nat.zero_div,Nat.zero_mod,ite_self]
  · exact gasRawSurplusByte_price ctx r hr hc i hi

end ZkFormal.NearV3.Assembly.RcptSkeleton
