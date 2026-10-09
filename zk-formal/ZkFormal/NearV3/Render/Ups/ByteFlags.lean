import ZkFormal.NearV3.Render.Ups.ByteWindows

/-! Copy and source-read selector formulas, independent of serialized byte contents. -/
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.UpsGen

set_option hygiene false in
macro "byte_kinds" : tactic => `(tactic| (
  rcases (show Q.kind = 0 ∨ Q.kind = 1 ∨ Q.kind = 2 ∨ Q.kind = 3 ∨ Q.kind = 4 ∨ Q.kind = 5 ∨
    Q.kind = 6 ∨ Q.kind = 7 ∨ Q.kind = 8 ∨ Q.kind = 9 ∨ Q.kind = 10 ∨ Q.kind = 11 by omega)
    with h | h | h | h | h | h | h | h | h | h | h | h))

theorem copy_tag (I : UpsInst) (Q : UpsPartI) (wi : Nat) (hk : Q.kind < 12) :
    cpV I Q 0 wi = kin Q [0,1,2,3,5,11] := by
  byte_kinds <;> simp [cpV,CpB,kin,ind,h]

theorem copy_prefix (I : UpsInst) (Q : UpsPartI) (st wi : Nat) (hk : Q.kind < 12)
    (hs : st = 1 ∨ st = 2) : cpV I Q st wi = kin Q [1,2,11] := by
  rcases hs with rfl | rfl <;> byte_kinds <;> simp [cpV,CpB,kin,ind,h]

theorem copy_key (I : UpsInst) (Q : UpsPartI) (wi : Nat) (hk : Q.kind < 12) :
    cpV I Q 3 wi = kin Q [1,2,6,7] := by
  byte_kinds <;> simp [cpV,CpB,kin,ind,h]

theorem copy_value (I : UpsInst) (Q : UpsPartI) (st wi : Nat) (hk : Q.kind < 12)
    (hs : st = 4 ∨ st = 5) : cpV I Q st wi = vcpV I Q := by
  rcases hs with rfl | rfl <;> byte_kinds <;> simp [cpV,CpB,VcpB,vcpV,kin,cin,ind,h]

theorem copy_bitmap (I : UpsInst) (Q : UpsPartI) (wi : Nat) (hk : Q.kind < 12) :
    cpV I Q 6 wi = kin Q [0,3,4,5] := by
  byte_kinds <;> simp [cpV,CpB,kin,ind,h]

theorem copy_child (I : UpsInst) (Q : UpsPartI) (wi : Nat) :
    cpV I Q 7 wi = 1-wfrV I Q 7 wi := by
  cases hw : WfrB I Q 7 wi <;> simp [cpV,CpB,wfrV,ind,hw]

theorem copy_mem (I : UpsInst) (Q : UpsPartI) (wi : Nat) : cpV I Q 8 wi = 0 := rfl

/-- Extra source reads used to rebuild headers and memory, apart from copied bytes. -/
def extraSum (I : UpsInst) (Q : UpsPartI) (st ix wi : Nat) : Int :=
  ind (st=0) * (kin Q [4,6,7] + xcpV I Q) +
  ind (st=1) * ind (ix=0) * kin Q [6,7] + ind (st=2) * kin Q [6,7] +
  ind (st=4) * ind (Q.kind=3) + ind (st=6) * ind (ix=0) * xcpV I Q +
  ind (st=8) * (1-ind (Q.kind=8)) + rdcV I Q st ix wi

theorem read_copy_extra (I : UpsInst) (Q : UpsPartI) (st ix wi : Nat)
    (hk : Q.kind < 12) (hs : st < 9) :
    rdV I Q st ix wi = cpV I Q st wi + extraSum I Q st ix wi := by
  rcases (show st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 ∨ st=6 ∨ st=7 ∨ st=8 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> byte_kinds <;>
    cases ht : TgtB I Q 7 wi <;>
    simp [rdV,cpV,extraSum,CpB,ExtraB,WfrB,VcpB,RdcB,rdcV,kin,xcpV,XcpB,ind,h,ht] <;>
    (repeat' split) <;> omega

end ZkFormal.NearV3.Render.UpsGen
