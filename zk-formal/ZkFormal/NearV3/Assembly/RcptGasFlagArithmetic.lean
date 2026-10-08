import ZkFormal.NearV3.Assembly.RcptGasBorrow
import ZkFormal.NearV3.Assembly.RcptNativeFlags

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.Air RcptV3
open ZkFormal.Near.Render RcptGen RcptP

def gasDifferenceSum (ctx : ApplyCtx) (r : Receipt) (n : Nat) : Nat :=
  sumR (gasDifference ctx r) n

theorem gasDifferenceSum_bound (ctx : ApplyCtx) (r : Receipt) (n : Nat) :
    gasDifferenceSum ctx r n≤255*n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have hh := gasDifference_lt ctx r n
    change gasDifferenceSum ctx r n+gasDifference ctx r n≤255*(n+1)
    omega

private theorem sumR_zero_V (f : Nat→Nat) : ∀n,sumR f n=0→V f n=0
  | 0,_=>rfl
  | n+1,h=>by
    change sumR f n+f n=0 at h
    have hf : f n=0 := by omega
    rw [V,sumR_zero_V f n (by omega),hf]
    simp

theorem gasDifferenceSum_refund_nonzero (ctx : ApplyCtx) (r : Receipt)
    (hg : r.gasPrice<256^16) (hc : ctx.gasPrice<256^16)
    (hr : nativeRefund ctx r=true) : gasDifferenceSum ctx r 16≠0 := by
  have hge := nativeRefund_price ctx r hr
  have hp : nativeSurplus ctx r≠0 := by
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp hr).2
  have hva : V (gasByte r.gasPrice) 16=r.gasPrice := V_leBytes_of (Nat.le_refl _) hg
  have hvb : V (gasByte ctx.gasPrice) 16=ctx.gasPrice := V_leBytes_of (Nat.le_refl _) hc
  have hv := V_bdig (gasByte r.gasPrice) (gasByte ctx.gasPrice) 0
    (gasByte_lt _) (gasByte_lt _) (by decide) (n:=16) (by rw [hva,hvb];omega)
  rw [hva,hvb,Nat.sub_zero] at hv
  intro hz
  have hzv := sumR_zero_V (gasDifference ctx r) 16 hz
  change V (gasDifference ctx r) 16=r.gasPrice-ctx.gasPrice at hv
  have he : r.gasPrice=ctx.gasPrice := by omega
  simp [nativeSurplus,he] at hp

private theorem bchain_same (a : Nat→Nat) : ∀n,bchain a a 0 n=0
  | 0=>rfl
  | n+1=>by simp [bchain,bchain_same a n]

theorem gasDifference_equal_price (ctx : ApplyCtx) (r : Receipt)
    (he : r.gasPrice=ctx.gasPrice) (i : Nat) : gasDifference ctx r i=0 := by
  simp [gasDifference,he,bdig,bchain_same]

theorem nativeRefund_false_equal_price (ctx : ApplyCtx) (r : Receipt)
    (hs : r.predecessorId≠AccountId.system) (hr : nativeRefund ctx r=false)
    (hge : ctx.gasPrice≤r.gasPrice) : r.gasPrice=ctx.gasPrice := by
  have hz : nativeSurplus ctx r=0 := by simpa [nativeRefund,hs] using hr
  simp only [nativeSurplus,Nat.min_eq_right hge,show Params.G=223182562500 from rfl] at hz
  omega

theorem gasDifference_no_refund (ctx : ApplyCtx) (r : Receipt)
    (hs : r.predecessorId≠AccountId.system) (hr : nativeRefund ctx r=false)
    (hge : ctx.gasPrice≤r.gasPrice) (i : Nat) : gasDifference ctx r i=0 :=
  gasDifference_equal_price ctx r (nativeRefund_false_equal_price ctx r hs hr hge) i

end ZkFormal.NearV3.Assembly.RcptSkeleton
