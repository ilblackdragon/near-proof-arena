import ZkFormal.NearV3.Render.Ups.MemUpScalars

namespace ZkFormal.NearV3.Render.UpsGen

private theorem prefix_scalars (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) :
    (Q.kind=5 → pfx (X1V I Q) 8=pfx (memRb Q) 8 ∧ pfx (EinV I Q) 8=102+L I) ∧
    (Q.kind=6 → pfx (X1V I Q) 8=0 ∧ pfx (EinV I Q) 8=100+2*Q.qhk+pfx (slb Q) 8) ∧
    (Q.kind=7 → pfx (X1V I Q) 8=pfx (memRb Q) 8-(50+2*Q.phk) ∧ pfx (EinV I Q) 8=50+2*Q.qhk) ∧
    (Q.kind=8 → pfx (X1V I Q) 8=0 ∧ pfx (EinV I Q) 8=102+L I) ∧
    (Q.kind=9 → pfx (X1V I Q) 8=Q.mB ∧ pfx (EinV I Q) 8=50+2*Q.qhk) := by
  rw [memory_subtraction_scalar I Q hL,memory_base_scalar I Q hL]
  repeat' apply And.intro
  all_goals intro hk; simp [useAV,bNV,bLV,cOV,cSV,CcV,eLV,eSV,KcV,kin,xcpV,XcpB,ind,hk]

theorem rbi_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) (hk : Q.kind=5)
    (m : Nat) (hm : pfx (memRb Q) 8=(m:Int)) :
    RV I (withMemorySign I Q)=((m+102+L I:Nat):Int) := by
  rw [withMemorySign_RV]
  obtain ⟨ha,he⟩ := (prefix_scalars I Q hL).1 hk
  rw [ha,he,hm]; split <;> omega

theorem mvl_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) (hk : Q.kind=6)
    (old : Nat) (ho : pfx (slb Q) 8=(old:Int)) :
    RV I (withMemorySign I Q)=((100+2*Q.qhk+old:Nat):Int) := by
  rw [withMemorySign_RV]
  obtain ⟨ha,he⟩ := (prefix_scalars I Q hL).2.1 hk
  rw [ha,he,ho]; omega

theorem mve_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) (hk : Q.kind=7)
    (m : Nat) (hm : pfx (memRb Q) 8=(m:Int)) :
    RV I (withMemorySign I Q)=((50+2*Q.qhk+(m-(50+2*Q.phk)):Nat):Int) := by
  rw [withMemorySign_RV]
  obtain ⟨ha,he⟩ := (prefix_scalars I Q hL).2.2.1 hk
  rw [ha,he,hm]; split <;> omega

theorem nlf_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) (hk : Q.kind=8) :
    RV I (withMemorySign I Q)=((102+L I:Nat):Int) := by
  rw [withMemorySign_RV]
  obtain ⟨ha,he⟩ := (prefix_scalars I Q hL).2.2.2.1 hk
  rw [ha,he]; omega

theorem wex_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24) (hk : Q.kind=9) :
    RV I (withMemorySign I Q)=((50+2*Q.qhk+Q.mB:Nat):Int) := by
  rw [withMemorySign_RV]
  obtain ⟨ha,he⟩ := (prefix_scalars I Q hL).2.2.2.2 hk
  rw [ha,he]; split <;> omega
end ZkFormal.NearV3.Render.UpsGen
