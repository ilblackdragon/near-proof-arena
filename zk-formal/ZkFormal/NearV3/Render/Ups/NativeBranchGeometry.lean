import ZkFormal.NearV3.Render.Ups.TreeBranchContexts
import ZkFormal.NearV3.Render.Ups.TreeBranchOccupancy
import ZkFormal.NearV3.Render.Ups.TreeBranchInput
import ZkFormal.NearV3.Render.Ups.TreeSources

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render

/-- Every actual RDB part preserves ordinary branch occupancy and produces a
well-formed serialized node, even when exact native memory exceeds u64. -/
theorem traceUpsert_branch_geometry {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (hw : t.wf=true) {p : TreePart}
    (hp : p∈run.parts) (hkind : p.kind=.RDB) (n : Nat) :
    ∃ sv kids mem outKids outMem,
      p.source=.branch sv kids mem ∧ p.output=.branch sv outKids outMem ∧
      (treeKids kids).length=16 ∧
      kidOccupancy (treeKids outKids)=kidOccupancy (viewKids n kids) ∧
      (NodeV3.branch (sv.map treeSlot) (treeKids outKids) ((u64 outMem).map UInt8.toNat)).wf := by
  obtain ⟨sv,kids,mem,rest,v,inner,hsrc,hout,hcall,hi⟩ :=
    traceUpsert_rdbContexts t key value run hr p hp hkind
  have hsw : (PTrie.branch sv kids mem).wf=true := by
    have hs := (traceUpsert_sources t key value run hw hr).2 p hp
    simpa only [hsrc] using hs
  have hcs : Kids.wf kids 16=true := by
    simp only [PTrie.wf,Bool.and_eq_true] at hsw
    exact hsw.1.2
  have hsrcwf := treeNode_wf hsw rfl
  have hd := traceKids_output_wf hcall hcs
  refine ⟨sv,kids,mem,inner.output,mem+inner.newMem-inner.oldMem,hsrc,hout,hsrcwf.1,?_,?_⟩
  · rw [viewKids_occupancy]
    exact traceKids_occupancy _ _ _ _ _ _ _ hcall hi
  · exact ⟨hd.1,hsrcwf.2.1,hd.2,by simp⟩
end ZkFormal.NearV3.Render.UpsGen
