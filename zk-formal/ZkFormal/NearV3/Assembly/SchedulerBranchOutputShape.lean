import ZkFormal.NearV3.Assembly.SchedulerBranchContexts
import ZkFormal.NearV3.Render.Ups.TreeBranchInput
import ZkFormal.NearV3.Render.Ups.TreeSources

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near ZkFormal.Near.Render

/-- Actual branch insertions and replacements both produce ordinary serialized
child widths. No exact-u64 output-memory or recursive output-wf is required. -/
theorem traceUpsert_branch_output_shape {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (hw : root.wf=true) {p : TreePart}
    (hp : p∈run.parts) (hk : p.kind=.RDB ∨ p.kind=.RBI) :
    ∃sv kids mem,p.output=.branch sv kids mem ∧ (treeKids kids).length=16 ∧
      (∀k∈treeKids kids,k.wf) ∧ (∀s∈sv,s.valueRef.length=36) := by
  obtain ⟨sv,kids,mem,rest,value,inner,hsrc,hout,hcall⟩:=
    traceUpsert_branchContexts root key v run hr p hp hk
  have hsw:=(traceUpsert_sources root key v run hw hr).2 p hp
  rw [hsrc] at hsw
  have hcs:Kids.wf kids 16=true:=by
    simp only [PTrie.wf,Bool.and_eq_true] at hsw
    exact hsw.1.2
  have hd:=traceKids_output_wf hcall hcs
  refine ⟨sv,inner.output,mem+inner.newMem-inner.oldMem,hout,hd.1,hd.2,?_⟩
  cases sv with
  | none=>simp
  | some s=>
    intro x hx
    simp only [Option.mem_some_iff] at hx
    subst x
    cases s <;> simp_all [PTrie.wf,slotOk,Slot.valueRef]

end ZkFormal.NearV3.Assembly
