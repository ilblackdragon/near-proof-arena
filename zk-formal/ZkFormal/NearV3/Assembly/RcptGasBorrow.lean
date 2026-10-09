import ZkFormal.NearV3.Assembly.RcptSystemGasDomain
import ZkFormal.Near.Render.Proof.RcptNat

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.Air RcptV3
open ZkFormal.Near.Render RcptGen RcptP

/-- Byte source shared with the native u128 wire encoding. -/
def gasByte (v i : Nat) : Nat := (leBytes 16 v).getD i 0

def gasBorrow (ctx : ApplyCtx) (r : Receipt) : Nat→Nat :=
  bchain (gasByte r.gasPrice) (gasByte ctx.gasPrice) 0

def gasDifference (ctx : ApplyCtx) (r : Receipt) (i : Nat) : Nat :=
  bdig (gasByte r.gasPrice) (gasByte ctx.gasPrice) 0 i

theorem gasByte_native (v i : Nat) : gasByte v i=((u128 v).getD i 0).toNat := by
  simp only [gasByte,leBytes,toNats,u128,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (leN 16 v)[i]? <;> rfl

theorem gasByte_lt (v i : Nat) : gasByte v i<256 := leBytes_getD_lt _ _ _

theorem gasBorrow_zero (ctx : ApplyCtx) (r : Receipt) : gasBorrow ctx r 0=0 := rfl

theorem gasBorrow_le (ctx : ApplyCtx) (r : Receipt) (i : Nat) : gasBorrow ctx r i≤1 :=
  bchain_le _ _ _ i (by decide)

theorem gasDifference_lt (ctx : ApplyCtx) (r : Receipt) (i : Nat) : gasDifference ctx r i<256 :=
  bdig_lt _ _ _ (gasByte_lt _) (gasByte_lt _) (by decide) i

theorem gasDifference_step (ctx : ApplyCtx) (r : Receipt) (i : Nat) :
    gasByte r.gasPrice i+256*gasBorrow ctx r (i+1)=
      gasByte ctx.gasPrice i+gasBorrow ctx r i+gasDifference ctx r i :=
  (bdig_step _ _ _ (gasByte_lt _) (gasByte_lt _) (by decide) i).1

theorem gasBorrow_final (ctx : ApplyCtx) (r : Receipt)
    (hr : r.gasPrice<256^16) (hc : ctx.gasPrice<256^16) :
    gasBorrow ctx r 16=if ctx.gasPrice≤r.gasPrice then 0 else 1 := by
  have hh := bchain_final (gasByte r.gasPrice) (gasByte ctx.gasPrice) 0
    (gasByte_lt _) (gasByte_lt _) (by decide) 16
  have hvr : V (gasByte r.gasPrice) 16=r.gasPrice := V_leBytes_of (Nat.le_refl _) hr
  have hvc : V (gasByte ctx.gasPrice) 16=ctx.gasPrice := V_leBytes_of (Nat.le_refl _) hc
  change gasBorrow ctx r 16=_ at hh
  rw [hvr,hvc,Nat.add_zero] at hh
  rw [hh]
  split <;> split <;> omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
