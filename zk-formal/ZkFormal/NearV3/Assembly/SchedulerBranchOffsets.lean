import ZkFormal.NearV3.Assembly.NativeSerializedDigests
import ZkFormal.NearV3.Render.Ups.BranchBoundaryCount
import ZkFormal.NearV3.Render.Ups.BranchWindowInput

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near ZkFormal.Near.Render

/-- Native child selection has the same occupied slot in the shallow serializer. -/
theorem treeKids_selected (kids : Kids) (slot : Nat) (child : PTrie)
    (hc : nativeChildAt kids slot=some child) :
    (treeKids kids)[slot]?=some (treeKid child) := by
  cases kids with
  | nil=>simp [nativeChildAt] at hc
  | none rest=>
    cases slot with
    | zero=>simp [nativeChildAt] at hc
    | succ n=>exact treeKids_selected rest n child hc
  | some c rest=>
    cases slot with
    | zero=>simp only [nativeChildAt,Option.some.injEq] at hc;subst child;rfl
    | succ n=>exact treeKids_selected rest n child hc
termination_by kids

/-- Each preceding occupied child contributes its actual 32-byte hash. There
is no assumption that the trie is flat or structurally deduplicated. -/
theorem childHashOffset_cid (kids : Kids) (slot : Nat)
    (hw : ∀k∈treeKids kids,k.wf) :
    childHashOffset kids slot=(branchCidBytes ((treeKids kids).take slot)).length := by
  rw [branchCidBytes_length]
  cases kids with
  | nil=>simp [childHashOffset,treeKids]
  | none rest=>
    cases slot with
    | zero=>simp [childHashOffset,treeKids]
    | succ n=>
      have hh:=childHashOffset_cid rest n (fun k hk=>hw k (by simp [treeKids,hk]))
      rw [branchCidBytes_length] at hh
      simpa [childHashOffset,treeKids] using hh
  | some c rest=>
    cases slot with
    | zero=>simp [childHashOffset,treeKids]
    | succ n=>
      have hh:=childHashOffset_cid rest n (fun k hk=>hw k (by simp [treeKids,hk]))
      rw [branchCidBytes_length] at hh
      have hc:=hw (treeKid c) (by simp [treeKids])
      have hl:c.hashOf.length=32:=by simpa [treeKid,NKid.wf] using hc
      simp only [childHashOffset,treeKids,List.take_succ_cons,List.filter_cons]
      simp only [show decide (treeKid c≠NKid.none)=true by simp [treeKid],ite_true,List.length_cons]
      omega
termination_by kids

/-- Native boundary slots become the exact first/last serialized digest window. -/
theorem childHashOffset_boundary (kids : Kids) (sd : Nat) (child : PTrie)
    (hlen : (treeKids kids).length=16) (hw : ∀k∈treeKids kids,k.wf)
    (hs : sd=0∨sd=1) (hc : nativeChildAt kids (edgeSlot sd)=some child) :
    childHashOffset kids (edgeSlot sd)=
      32*(if sd==1 then (NodeGen3.branchWins (treeKids kids)).length-1 else 0) := by
  rw [childHashOffset_cid kids (edgeSlot sd) hw,branchWins_count]
  exact boundary_cid_prefix (treeKids kids) sd hlen hs (treeKid child)
    (treeKids_selected kids (edgeSlot sd) child hc) (by simp [treeKid])

end ZkFormal.NearV3.Assembly
