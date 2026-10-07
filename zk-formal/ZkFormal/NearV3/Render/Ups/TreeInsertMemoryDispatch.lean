import ZkFormal.NearV3.Render.Ups.TreeInsertDispatch
import ZkFormal.NearV3.Render.Ups.TreeMemoryPrefix
import ZkFormal.NearV3.Render.Ups.TreeValueMemoryDispatch

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

def trace_insert_byteMemory {value : Option Slot} {kids : Kids} {mem slot : Nat}
    {key : List Nat} {v : Bytes} {run : KidsRun}
    (hr : traceKids (.branch value kids mem) (slot::key) kids slot key v=some run)
    (hi : run.inserted=true) (hw : (PTrie.branch value kids mem).wf=true)
    (hkey : slot::key=[0,15] ∨ slot::key=[15]) (hv : v.length<2^24) (baseI : UpsInst)
    {part : TreePart} (hp : part∈(closeBranchRun value kids mem slot run).parts)
    (base : UpsPartI) {Q : UpsPartI} (he : encodeTreePart base part=some Q)
    (hm : base.mB<2^74)
    (hchild : ∀ b∈(child (traceInstance baseI (closeBranchRun value kids mem slot run) v) Q).pb,b<256) :
    ByteMemoryInput (traceInstance baseI (closeBranchRun value kids mem slot run) v)
      (withMemorySign (traceInstance baseI (closeBranchRun value kids mem slot run) v) Q) := by
  let I := traceInstance baseI (closeBranchRun value kids mem slot run) v
  let data := trace_insert_byteInput hr hi hw hkey baseI hp base he
  refine ⟨data.withMemorySign,?_⟩
  change MemOk I (withMemorySign I Q)
  have hd := traceKids_inserted _ _ _ _ _ _ _ hr hi
  have hshort : key.length≤1 := by
    rcases hkey with hh|hh
    · obtain ⟨rfl,rfl⟩ := List.cons.inj hh; decide
    · obtain ⟨rfl,rfl⟩ := List.cons.inj hh; decide
  have hc : I.ci<11 := by
    simp [I,traceInstance,closeBranchRun,pushPart,hd.2.2,terminalRun,UCase.ix]
  have hL : L I<2^24 := by simpa [I,traceInstance,L] using hv
  have hmb : Q.mB<2^74 := by
    unfold encodeTreePart at he
    cases hs : treeNode part.source <;> cases ht : treeNode part.output <;> simp [hs,ht] at he
    subst Q
    exact hm
  have hparts := hp
  simp only [closeBranchRun,pushPart,hd.2.2,terminalRun,List.mem_append,List.mem_singleton] at hparts
  have hhead : Q.qhk<2^22 ∧ Q.phk<2^22 := by
    rcases hparts with rfl|rfl <;>
      simp [encodeTreePart,treeNode,newLeaf] at he <;> subst Q <;>
      simp [encodePart,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf] <;> omega
  apply data.native_memOk he hc hhead.1 hhead.2 hL hchild hmb
  rcases hparts with rfl|rfl
  · exact treeNlf_memory I base Q (.branch value kids mem) key v he hshort rfl hL
  · have hencode : encodeTreePart base ⟨.RBI,.branch value kids mem,
        .branch value run.output (mem+leafMem key v.length),slot⟩=some Q := by
      simpa [hi,hd.1,hd.2.1] using he
    have ht := treeRbi_memory I base Q value kids run.output mem slot key v hencode hw hshort rfl hL
    simpa [hi,hd.1,hd.2.1,PTrie.memD,PTrie.mem?] using ht
end ZkFormal.NearV3.Render.UpsGen
