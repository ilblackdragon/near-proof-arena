import ZkFormal.NearV3.Assembly.SchedulerBranchOffsets
import ZkFormal.NearV3.Render.Ups.SplitKidCounts

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near ZkFormal.Near.Render

/-- A selected native boundary child is read at the exact branch field offset,
including the optional value header and all occupied preceding children. -/
theorem native_branch_field_slice {p : TreePart} {sv : Option Slot} {kids : Kids} {mem : Nat}
    (ho : p.output=.branch sv kids mem) {base Q : UpsPartI}
    (he : encodeTreePart base p=some Q) (sd : Nat) (hs : sd=0∨sd=1)
    (hlen : (treeKids kids).length=16) (hw : ∀k∈treeKids kids,k.wf)
    (hv : ∀s∈sv,s.valueRef.length=36) {child : PTrie}
    (hc : nativeChildAt kids (edgeSlot sd)=some child) (hh : child.hashOf.length=32) :
    ((nodeEnc p.output).drop ((if Q.ty=2 then 3 else 39)+
      32*(if sd==1 then nWin Q.shape-1 else 0))).take 32=child.hashOf := by
  have hcount : nWin Q.shape=(NodeGen3.branchWins (treeKids kids)).length := by
    unfold encodeTreePart at he
    rw [ho,treeNode] at he
    cases hsrc:treeNode p.source <;> simp [hsrc] at he
    subst Q
    rw [encodePart_windows]
    rfl
  have hty:=encodeTreePart_type he
  have hprefix : (branchHashPrefix sv kids).length=(if Q.ty=2 then 3 else 39) := by
    cases sv with
    | none=>
      have ht:Q.ty=2:=by simpa [ho,nativeNodeType] using hty
      simp [branchHashPrefix,ht]
    | some s=>
      have hv':s.valueRef.length=36:=hv s (by simp)
      have ht:Q.ty=3:=by simpa [ho,nativeNodeType] using hty
      simp [branchHashPrefix,hv',ht]
  have hoff:=childHashOffset_boundary kids sd child hlen hw hs hc
  rw [←hcount] at hoff
  rw [ho,←hoff,←hprefix]
  exact branch_child_digest_window sv kids mem (edgeSlot sd) child hc hh

end ZkFormal.NearV3.Assembly
