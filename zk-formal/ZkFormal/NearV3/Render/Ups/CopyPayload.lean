import ZkFormal.NearV3.Render.Ups.CopyFields

namespace ZkFormal.NearV3.Render.UpsGen

def bitmapDelta (patch : Bool) (ts ix : Nat) : Int :=
  if patch then (if ix=0 then ind (ts=1) else 128*ind (ts≠1)) else 0

theorem FieldPayloadEdit.byte {patch : Bool} {x ts ix : Nat} {src dst : List Nat}
    (h : FieldPayloadEdit patch x src dst) (hx : x=if ts=1 then 0 else 15)
    (hi : patch=true → ix<2) :
    (dst.getD ix 0 : Int)=(src.getD ix 0 : Int)+bitmapDelta patch ts ix := by
  cases h with
  | preserve x bytes => simp [bitmapDelta]
  | insert x old hxb ho hc =>
    have hi' := hi rfl
    rcases (show ix=0 ∨ ix=1 by omega) with rfl | rfl <;>
      by_cases ht : ts=1 <;> simp [hx,ht,bitmapDelta,ind] at hc ⊢ <;> omega

end ZkFormal.NearV3.Render.UpsGen
