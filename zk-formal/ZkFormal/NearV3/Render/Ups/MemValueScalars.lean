import ZkFormal.NearV3.Render.Ups.MemNative

/-! Value-terminal memory arithmetic agrees with native natural subtraction,
including u64 serialization overflow. -/
namespace ZkFormal.NearV3.Render.UpsGen

private theorem terminal_scalars (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) :
    (Q.kind=2 → pfx (X1V I Q) 8=0 ∧ pfx (EinV I Q) 8=100+2*Q.qhk+L I) ∧
    (Q.kind=3 → pfx (X1V I Q) 8=pfx (memRb Q) 8+L I-pfx (slb Q) 8 ∧ pfx (EinV I Q) 8=0) ∧
    (Q.kind=4 → pfx (X1V I Q) 8=pfx (memRb Q) 8 ∧ pfx (EinV I Q) 8=50+L I) := by
  rw [memory_subtraction_scalar I Q hL,memory_base_scalar I Q hL]
  repeat' apply And.intro
  all_goals intro hk; simp [useAV,bNV,bLV,cOV,cSV,CcV,eLV,eSV,KcV,kin,xcpV,XcpB,ind,hk]

theorem rlp_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) (hk : Q.kind=2) :
    RV I (withMemorySign I Q)=100+2*Q.qhk+L I := by
  rw [withMemorySign_RV]
  obtain ⟨ha,he⟩ := (terminal_scalars I Q hL).1 hk
  rw [ha,he]; omega

theorem rbr_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) (hk : Q.kind=3)
    (m old : Nat) (hm : pfx (memRb Q) 8=(m:Int)) (ho : pfx (slb Q) 8=(old:Int)) :
    RV I (withMemorySign I Q)=((m+L I-old:Nat):Int) := by
  rw [withMemorySign_RV]
  obtain ⟨ha,he⟩ := (terminal_scalars I Q hL).2.1 hk
  rw [ha,he,hm,ho]
  split <;> omega

theorem rbv_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) (hk : Q.kind=4)
    (m : Nat) (hm : pfx (memRb Q) 8=(m:Int)) :
    RV I (withMemorySign I Q)=((m+50+L I:Nat):Int) := by
  rw [withMemorySign_RV]
  obtain ⟨ha,he⟩ := (terminal_scalars I Q hL).2.2 hk
  rw [ha,he,hm]
  split <;> omega
end ZkFormal.NearV3.Render.UpsGen
