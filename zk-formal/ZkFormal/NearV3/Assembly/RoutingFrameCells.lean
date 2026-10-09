import ZkFormal.NearV3.Assembly.RoutingFrameBits
namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
@[simp] theorem frame_cell_0 (f : RouteFrame) : frameCell f sV=(if f.atEnd then 0 else 1) := rfl
@[simp] theorem frame_cell_1 (f : RouteFrame) : frameCell f sRID=(if f.atEnd then 1 else 0) := rfl
@[simp] theorem frame_cell_2 (f : RouteFrame) : frameCell f fs=(if f.first || f.atEnd then 1 else 0) := rfl
@[simp] theorem frame_cell_3 (f : RouteFrame) : frameCell f idx=((f.pos:Fp)) := rfl
@[simp] theorem frame_cell_4 (f : RouteFrame) : frameCell f Lv=((f.pos:Fp)) := rfl
@[simp] theorem frame_cell_5 (f : RouteFrame) : frameCell f iB=((f.pos:Fp)) := rfl
@[simp] theorem frame_cell_6 (f : RouteFrame) : frameCell f b=((f.value.toNat:Fp)) := rfl
@[simp] theorem frame_cell_7 (f : RouteFrame) : frameCell f vB=((f.value.toNat:Fp)) := rfl
@[simp] theorem frame_cell_8 (f : RouteFrame) : frameCell f loB=((f.lower.toNat:Fp)) := rfl
@[simp] theorem frame_cell_9 (f : RouteFrame) : frameCell f hiB=((f.upper.toNat:Fp)) := rfl
@[simp] theorem frame_cell_10 (f : RouteFrame) : frameCell f hnB=(if f.missingUpper then 1 else 0) := rfl
@[simp] theorem frame_cell_11 (f : RouteFrame) : frameCell f eqL=(if f.equalLower then 1 else 0) := rfl
@[simp] theorem frame_cell_12 (f : RouteFrame) : frameCell f eqH=(if f.equalUpper then 1 else 0) := rfl
@[simp] theorem frame_cell_13 (f : RouteFrame) : frameCell f gBd=(if f.equalLower || f.equalUpper then 1 else 0) := rfl
@[simp] theorem frame_cell_14 (f : RouteFrame) : frameCell f eL=(if f.value=f.lower then 1 else 0) := rfl
@[simp] theorem frame_cell_15 (f : RouteFrame) : frameCell f eH=(if f.upper=f.value then 1 else 0) := rfl
@[simp] theorem frame_cell_16 (f : RouteFrame) : frameCell f iL=frameInverse f.value f.lower := by
  unfold frameCell
  exact if_pos rfl
@[simp] theorem frame_cell_17 (f : RouteFrame) : frameCell f iH=frameInverse f.upper f.value := by
  unfold frameCell
  rw [if_neg (by decide : iH ≠ iL)]
  exact if_pos rfl
@[simp] theorem frame_cell_18 (f : RouteFrame) : frameCell f (xb 28)=(frameBit (f.value.toNat+255-f.lower.toNat) 8) := rfl
@[simp] theorem frame_cell_19 (f : RouteFrame) : frameCell f (xb 37)=(frameBit (f.upper.toNat+255-f.value.toNat) 8) := rfl
@[simp] theorem frame_next_lower (f : RouteFrame) : frameNext f eqL=(if f.equalLower && (f.value==f.lower) then 1 else 0) := rfl
@[simp] theorem frame_next_upper (f : RouteFrame) : frameNext f eqH=(if f.equalUpper && (f.upper==f.value) then 1 else 0) := rfl
end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
