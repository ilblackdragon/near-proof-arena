import ZkFormal.NearV3.Render.Ups.TreeInsertTrace
import ZkFormal.NearV3.Render.Ups.TreePrefixInput
import ZkFormal.NearV3.Render.Ups.TreeMetadata

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

def closeBranchRun (value : Option Slot) (kids : Kids) (mem slot : Nat) (run : KidsRun) : TreeRun :=
  pushPart run.inner ⟨if run.inserted then .RBI else .RDB,.branch value kids mem,
    .branch value run.output (mem+run.newMem-run.oldMem),slot⟩

theorem traceUpsert_closeBranch {value : Option Slot} {kids : Kids} {mem slot : Nat}
    {key : List Nat} {v : Bytes} {run : KidsRun}
    (hr : traceKids (.branch value kids mem) (slot::key) kids slot key v=some run) :
    traceUpsert (.branch value kids mem) (slot::key) v=some (closeBranchRun value kids mem slot run) := by
  simp [traceUpsert,hr,closeBranchRun]

/-- Missing-branch dispatch derives the edge side and fresh suffix from the
actual remaining fixed-key suffix; no per-byte constraints are hypotheses. -/
def trace_insert_byteInput {value : Option Slot} {kids : Kids} {mem slot : Nat}
    {key : List Nat} {v : Bytes} {run : KidsRun}
    (hr : traceKids (.branch value kids mem) (slot::key) kids slot key v=some run)
    (hi : run.inserted=true) (hw : (PTrie.branch value kids mem).wf=true)
    (hkey : slot::key=[0,15] ∨ slot::key=[15]) (baseI : UpsInst)
    {part : TreePart} (hp : part∈(closeBranchRun value kids mem slot run).parts)
    (base : UpsPartI) {Q : UpsPartI} (he : encodeTreePart base part=some Q) :
    ByteInput (traceInstance baseI (closeBranchRun value kids mem slot run) v) Q := by
  let I := traceInstance baseI (closeBranchRun value kids mem slot run) v
  change ByteInput I Q
  have hin := (traceKids_inserted _ _ _ _ _ _ _ hr hi).2.2
  have hmeta : (1≤I.ts ∧ I.ts≤3) ∧ I.x<16 ∧
      key=[0,15].drop I.ts ∧ slot=edgeSlot (insertSide I) := by
    rcases hkey with h|h
    · obtain ⟨rfl,rfl⟩ := List.cons.inj h
      simp [I,traceInstance,closeBranchRun,pushPart,hin,terminalRun,TreeRun.splitCursor,
        TreeRun.consumed,TreeRun.splitNibble,edgeSlot,insertSide]
    · obtain ⟨rfl,rfl⟩ := List.cons.inj h
      simp [I,traceInstance,closeBranchRun,pushPart,hin,terminalRun,TreeRun.splitCursor,
        TreeRun.consumed,TreeRun.splitNibble,edgeSlot,insertSide]
  simp only [closeBranchRun,pushPart,hin,terminalRun,List.mem_append,List.mem_singleton] at hp
  by_cases hp1 : part.kind=.NLF
  · have hp0 := hp.resolve_right (by intro hh; rw [hh] at hp1; simp [hi] at hp1)
    subst part
    apply treeNlf_byteInput I base (.branch value kids mem) v Q
      (by simpa only [hmeta.2.2.1] using he) hw rfl hmeta.1 hmeta.2.1
  · have hp2 := hp.resolve_left (by intro hh; apply hp1; rw [hh])
    subst part
    apply treeRbi_byteInput I base value kids mem key v run Q
      (by simpa only [← hmeta.2.2.2] using hr) hi
      (by simpa only [hi,ite_true,← hmeta.2.2.2] using he) hw hmeta.1 hmeta.2.1
end ZkFormal.NearV3.Render.UpsGen
