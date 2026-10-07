import ZkFormal.NearV3.Render.Ups.BranchCidWindows
import ZkFormal.NearV3.Render.Ups.WindowStart
import ZkFormal.NearV3.Render.Ups.WindowInput
import ZkFormal.NearV3.Render.Ups.EncodePart
import ZkFormal.NearV3.Render.Ups.KidOccupancy
import ZkFormal.NearV3.Render.Node.Seq

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

theorem branchWins_count (kids : List NKid) :
    (NodeGen3.branchWins kids).length=(kids.filter (fun k=>k≠.none)).length := by
  change (NodeGen3.branchWins kids).length=NodeGen3.popK kids
  rw [NodeGen3.branchWins_eq]
  simp only [NodeGen3.winsOf,List.length_map,List.length_zip,List.length_range',Nat.min_self]
  exact NodeGen3.popK_eq kids

/-- Replacing an occupied boundary child preserves bitmap order and reads that
child's source ID at the selected window. The inputs describe node allocation
and ordinary child occupancy, rather than an AIR equality. -/
theorem branch_window_ok (I : UpsInst) (base : UpsPartI) (value : Option NSlot3)
    (before after dstKids : List NKid) (oldMem newMem : List Nat)
    (cid clen cres : Nat) (pre post : List Nat)
    (hk : base.kind=0) (hc : base.cN=cid)
    (hside : (base.sd=0 ∧ before=[]) ∨ (base.sd=1 ∧ after=[]))
    (hocc : kidOccupancy dstKids=kidOccupancy (before ++ .node cid clen cres pre post :: after))
    (hp : base.pcid=sourceCidBytes (.branch value (before ++ .node cid clen cres pre post :: after) oldMem))
    (hw : (NodeV3.branch value dstKids newMem).wf) :
    WindowOk I (encodePart base (.branch value (before ++ .node cid clen cres pre post :: after) oldMem)
      (.branch value dstKids newMem)) := by
  let src := NodeV3.branch value (before ++ .node cid clen cres pre post :: after) oldMem
  let dst := NodeV3.branch value dstKids newMem
  let Q := encodePart base src dst
  have hf : FieldsOk Q := encodePart_fields base src dst hw
  have hhead : fieldsLen (nodeHeader Q.ty Q.qhk)=(if value.isSome then 39 else 3) := by
    cases value <;> rfl
  have hn : nWin Q.shape=(before.filter (fun k=>k≠.none)).length+1+
      (after.filter (fun k=>k≠.none)).length := by
    change nWin (nonemptyFields (nodeRawShape dst))=_
    rw [nonempty_node_shape,nodeFields_windows]
    change (NodeGen3.branchWins dstKids).length=_
    rw [windows_eq_of_occupancy hocc,branchWins_count]
    simp only [List.filter_append,List.filter_cons,ne_eq,reduceCtorEq,not_false_eq_true,decide_true,ite_true,
      List.length_append,List.length_cons]
    omega
  constructor
  · intro hbad; change base.kind=10 at hbad; omega
  · intro p _ hs hi ht _
    have hpos := hf.target_start I hs hi ht
    have hs15 : S15B I Q=(base.sd==1) := by simp [S15B,Q,encodePart,hk]
    rw [hhead,hs15,hn] at hpos
    have hbefore : p=(if value.isSome then 39 else 3)+(branchCidBytes before).length := by
      rw [branchCidBytes_length]
      rcases hside with ⟨hsd,hbef⟩|⟨hsd,haft⟩
      · simp only [hsd,hbef,List.filter_nil,List.length_nil,beq_iff_eq,reduceCtorEq,ite_false,
          Nat.mul_zero,Nat.add_zero] at hpos ⊢
        exact hpos
      · simp only [hsd,haft,List.filter_nil,List.length_nil,beq_self_eq_true,ite_true,
          Nat.add_zero,Nat.add_sub_cancel] at hpos
        exact hpos
    have hread : (sposV I Q 7 0 (fieldAt Q.shape p).2.2.2 p).toNat=p := by
      simp [sposV,Q,encodePart,hk]
    change Q.pcid.getD (sposV I Q 7 0 (fieldAt Q.shape p).2.2.2 p).toNat 0=Q.cN
    rw [hread]
    change base.pcid.getD p 0=base.cN
    rw [hp,hc,hbefore]
    simpa only [Nat.add_zero] using sourceCidBytes_branch_after value before after oldMem
      cid clen cres pre post 0 (by decide)
end ZkFormal.NearV3.Render.UpsGen
