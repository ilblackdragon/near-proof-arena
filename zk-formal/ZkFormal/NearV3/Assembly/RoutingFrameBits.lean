import ZkFormal.NearV3.Assembly.RoutingFrameArithmetic

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem frameCell_lower_bit (f : RouteFrame) (j : Nat) (hj : j<9) :
    frameCell f (xb (20+j))=frameBit (f.value.toNat+255-f.lower.toNat) j := by
  have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
  rcases hh with h|h|h|h|h|h|h|h|h <;> subst j <;> rfl


theorem frameCell_upper_bit (f : RouteFrame) (j : Nat) (hj : j<9) :
    frameCell f (xb (29+j))=frameBit (f.upper.toNat+255-f.value.toNat) j := by
  have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
  rcases hh with h|h|h|h|h|h|h|h|h <;> subst j <;> rfl


theorem eval_frame_bits (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (off x len : Nat) (hc : ∀j,j<len → tr.cell t r (xb (off+j))=frameBit x j) :
    (bitsX off len).eval tr t r pub=Fp.ofNat (x%2^len) := by
  have hh : (bitsX off len).eval tr t r pub=Fp.ofNat (bitsVal (fun j=>(x/2^j)%2) 0 len) := by
    induction len with
    | zero => rfl
    | succ len ih =>
      unfold bitsX
      rw [bits_succ,eval_sum_append]
      change (bitsX off len).eval tr t r pub+_= _
      rw [ih (fun j hj=>hc j (by omega))]
      simp only [eval_sum_cons,eval_sum_nil,eval_smul,eval_c,hc len (by omega),frameBit,bitsVal,Nat.zero_add]
      change (↑(bitsVal (fun j=>(x/2^j)%2) 0 len):Fp) + ((↑(2^len:Nat):Fp) * ↑((x/2^len)%2)+0) = ↑(bitsVal (fun j=>(x/2^j)%2) 0 len + 2^len*((x/2^len)%2))
      simp only [natCast_add,natCast_mul]
      grind
  rw [hh,frame_bitsVal]

theorem frame_lower_bits (f : RouteFrame) (pub : List Fp) :
    (bitsX 20 9).eval (frameTrace f) 0 0 pub=
      (f.value.toNat:Fp)-(f.lower.toNat:Fp)+255 := by
  rw [eval_frame_bits _ _ _ _ _ _ _ (fun j hj=>frameCell_lower_bit f j hj)]
  rw [Nat.mod_eq_of_lt (frame_diff_bound f.value f.lower)]
  exact frame_diff_cast _ _

theorem frame_upper_bits (f : RouteFrame) (pub : List Fp) :
    (bitsX 29 9).eval (frameTrace f) 0 0 pub=
      (f.upper.toNat:Fp)-(f.value.toNat:Fp)+255 := by
  rw [eval_frame_bits _ _ _ _ _ _ _ (fun j hj=>frameCell_upper_bit f j hj)]
  rw [Nat.mod_eq_of_lt (frame_diff_bound f.upper f.value)]
  exact frame_diff_cast _ _

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
