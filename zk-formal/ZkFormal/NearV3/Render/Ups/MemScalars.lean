import ZkFormal.NearV3.Render.Ups.MemSign

/-! Scalar interpretation of the renderer's byte-limb memory arithmetic. -/
namespace ZkFormal.NearV3.Render.UpsGen

theorem pfx_sub (f g : Nat → Int) : ∀ n,
    pfx (fun i => f i-g i) n=pfx f n-pfx g n
  | 0 => by simp [pfx]
  | n+1 => by simp only [pfx,pfx_sub f g n,Int.sub_mul]; omega

theorem pfx_delta (x : Int) : pfx (fun i => ind (i=0)*x) 8=x := by
  simp [pfx,ind]

/-- The last exact limb retains all high bits, including overflow above u64. -/
theorem pfx_exact_limbs (x : Int) : pfx (limb x) 8=x := by
  simp only [pfx,limb,Int.reducePow,Nat.reduceLT,ite_true,ite_false,
    Int.zero_add,Int.mul_one,Int.ediv_one]
  omega

theorem pfx_value_length (I : UpsInst) (h : L I<2^24) : pfx (Lb I) 8=(L I:Int) := by
  simp only [pfx,Lb,Nat.reduceEqDiff,ite_true,ite_false,Int.reducePow,
    Int.zero_add,Int.mul_one,Int.zero_mul,Int.add_zero]
  omega

/-- The inside subtraction is the native scalar A+B-C expression. -/
theorem memory_subtraction_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) :
    pfx (X1V I Q) 8 =
      useAV I Q*pfx (memRb Q) 8 + (bNV I Q*(Q.mB:Int)+bLV Q*(L I:Int)) -
      (cOV Q*pfx (memByte (child I Q)) 8+cSV Q*pfx (slb Q) 8+CcV I Q) := by
  unfold X1V
  rw [pfx_sub,pfx_add]
  unfold Ai Bi Ci
  rw [pfx_mul,pfx_add,pfx_mul,pfx_mul,pfx_exact_limbs,pfx_value_length I hL,
    pfx_add,pfx_add,pfx_mul,pfx_mul,pfx_delta]

/-- The outside addend is the native fixed/value/retained-slot contribution. -/
theorem memory_base_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) :
    pfx (EinV I Q) 8=KcV I Q+eLV Q*(L I:Int)+eSV I Q*pfx (slb Q) 8 := by
  unfold EinV
  rw [pfx_add,pfx_add,pfx_delta,pfx_mul,pfx_mul,pfx_value_length I hL]
end ZkFormal.NearV3.Render.UpsGen
