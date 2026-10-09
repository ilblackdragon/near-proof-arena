import ZkFormal.NearV3.Render.Ups.MemPrefixScalars

namespace ZkFormal.NearV3.Render.UpsGen

theorem spb_fresh_some_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24)
    (hk : Q.kind=10) (hc : I.ci=5 ∨ I.ci=7) :
    RV I (withMemorySign I Q)=((100+L I+Q.mB:Nat):Int) := by
  rw [withMemorySign_RV,memory_subtraction_scalar I Q hL,memory_base_scalar I Q hL]
  rcases hc with hc|hc <;>
    simp [useAV,bNV,bLV,cOV,cSV,CcV,eLV,eSV,KcV,kin,cin,spRecv,xcpV,XcpB,ind,hk,hc] <;>
    omega

theorem spb_fresh_none_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24)
    (hk : Q.kind=10) (hc : I.ci=6 ∨ I.ci=9) :
    RV I (withMemorySign I Q)=((152+L I+Q.mB:Nat):Int) := by
  rw [withMemorySign_RV,memory_subtraction_scalar I Q hL,memory_base_scalar I Q hL]
  rcases hc with hc|hc <;>
    simp [useAV,bNV,bLV,cOV,cSV,CcV,eLV,eSV,KcV,kin,cin,spRecv,xcpV,XcpB,ind,hk,hc] <;>
    omega

theorem spb_value_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24)
    (hk : Q.kind=10) (hc : I.ci=4) (old : Nat) (ho : pfx (slb Q) 8=(old:Int)) :
    RV I (withMemorySign I Q)=((202+L I+old:Nat):Int) := by
  rw [withMemorySign_RV,memory_subtraction_scalar I Q hL,memory_base_scalar I Q hL]
  simp [useAV,bNV,bLV,cOV,cSV,CcV,eLV,eSV,KcV,kin,cin,spRecv,xcpV,XcpB,ind,hk,hc,ho]

theorem spb_child_some_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24)
    (hk : Q.kind=10) (hc : I.ci=8) (m : Nat) (hm : pfx (memRb Q) 8=(m:Int)) :
    RV I (withMemorySign I Q)=((100+L I+(m-(50+2*Q.phk)):Nat):Int) := by
  rw [withMemorySign_RV,memory_subtraction_scalar I Q hL,memory_base_scalar I Q hL]
  simp [useAV,bNV,bLV,cOV,cSV,CcV,eLV,eSV,KcV,kin,cin,spRecv,xcpV,XcpB,ind,hk,hc,hm]
  split <;> omega

theorem spb_child_none_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24)
    (hk : Q.kind=10) (hc : I.ci=10) (m : Nat) (hm : pfx (memRb Q) 8=(m:Int)) :
    RV I (withMemorySign I Q)=((152+L I+(m-(50+2*Q.phk)):Nat):Int) := by
  rw [withMemorySign_RV,memory_subtraction_scalar I Q hL,memory_base_scalar I Q hL]
  simp [useAV,bNV,bLV,cOV,cSV,CcV,eLV,eSV,KcV,kin,cin,spRecv,xcpV,XcpB,ind,hk,hc,hm]
  split <;> omega
end ZkFormal.NearV3.Render.UpsGen
