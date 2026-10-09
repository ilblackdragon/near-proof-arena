import ZkFormal.NearV3.Render.Ups.MemArith

/-! Construct the memory subtraction sign from ordinary serialized operands.
The renderer's sign bit is determined, rather than supplied as an AIR assumption. -/
namespace ZkFormal.NearV3.Render.UpsGen
set_option maxHeartbeats 3000000

def withMemorySign (I : UpsInst) (Q : UpsPartI) : UpsPartI :=
  {Q with neg:=if pfx (X1V I Q) 8<0 then 1 else 0}

@[simp] theorem withMemorySign_X1V (I : UpsInst) (Q : UpsPartI) :
    X1V I (withMemorySign I Q)=X1V I Q := by
  funext i
  simp only [X1V,Ai,Bi,Ci,useAV,bNV,bLV,cOV,cSV,memRb,child,slb,CcV,kin,cin,xcpV,XcpB,spRecv,withMemorySign]
  rfl
@[simp] theorem withMemorySign_EinV (I : UpsInst) (Q : UpsPartI) :
    EinV I (withMemorySign I Q)=EinV I Q := by
  funext i
  simp only [EinV,KcV,eLV,eSV,slb,kin,cin,xcpV,XcpB,withMemorySign]
  rfl

theorem withMemorySign_bit (I : UpsInst) (Q : UpsPartI) : (withMemorySign I Q).neg≤1 := by
  change (if pfx (X1V I Q) 8<0 then 1 else 0)≤1
  split <;> omega

theorem withMemorySign_TV (I : UpsInst) (Q : UpsPartI) :
    TV I (withMemorySign I Q)=if pfx (X1V I Q) 8<0 then -pfx (X1V I Q) 8 else pfx (X1V I Q) 8 := by
  unfold TV
  rw [withMemorySign_X1V]
  simp only [sigV,withMemorySign]
  split <;> simp

theorem withMemorySign_RV (I : UpsInst) (Q : UpsPartI) :
    RV I (withMemorySign I Q)=pfx (EinV I Q) 8 +
      (if pfx (X1V I Q) 8<0 then 0 else pfx (X1V I Q) 8) := by
  unfold RV
  rw [withMemorySign_EinV,withMemorySign_TV]
  simp only [withMemorySign]
  split <;> simp

/-- A bound on the actual signed subtraction yields the final carry bound. -/
theorem withMemorySign_bound (I : UpsInst) (Q : UpsPartI) (limit : Int)
    (hl : -limit<pfx (X1V I Q) 8) (hu : pfx (X1V I Q) 8<limit) :
    0≤TV I (withMemorySign I Q) ∧ TV I (withMemorySign I Q)<limit := by
  rw [withMemorySign_TV]
  split <;> omega
end ZkFormal.NearV3.Render.UpsGen
