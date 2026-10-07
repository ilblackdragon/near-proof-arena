import ZkFormal.NearV3.Render.Ups.TreeValueDispatch
import ZkFormal.NearV3.Render.Ups.TreeMemoryInput
import ZkFormal.NearV3.Render.Ups.ByteMemoryAssembly

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

/-- Actual value-terminal dispatch derives memory completeness, including both
header caps, rather than requiring an assumed case-specific scalar equation. -/
theorem trace_value_memOk {source : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert source key v=some run) (hw : source.wf=true)
    (hvterm : valueTerminal source key) (hk : key.length≤2) (hv : v.length<2^24)
    (baseI : UpsInst) {part : TreePart} (hp : part∈run.parts)
    (base : UpsPartI) {Q : UpsPartI} (he : encodeTreePart base part=some Q)
    (hchild : ∀ b∈(child (traceInstance baseI run v) Q).pb,b<256) :
    MemOk (traceInstance baseI run v) (withMemorySign (traceInstance baseI run v) Q) := by
  have hL : L (traceInstance baseI run v)<2^24 := by simpa [L,traceInstance] using hv
  cases source with
  | hash h => simp [valueTerminal] at hvterm
  | ext oldKey child mem => simp [valueTerminal] at hvterm
  | leaf oldKey old mem =>
    have hkey : oldKey=key := hvterm
    subst oldKey
    simp only [traceUpsert,ite_true,Option.some.injEq] at hr
    subst run
    simp only [terminalRun,List.mem_singleton] at hp
    subst part
    have hhead : Q.qhk<2^22 ∧ Q.phk<2^22 := by
      simp [encodeTreePart,treeNode,newLeaf] at he
      subst Q
      simp [encodePart,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf]
      omega
    apply treeRlp_memOk _ base Q key old mem v he hw rfl _ hhead.1 hhead.2 hL hchild
    change 0<11; decide
  | branch old kids mem =>
    have hkey : key=[] := hvterm
    subst key
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    simp only [terminalRun,List.mem_singleton] at hp
    subst part
    cases old with
    | none =>
      have he' := he
      simp [encodeTreePart,treeNode] at he'
      have hhead : Q.qhk<2^22 ∧ Q.phk<2^22 := by
        subst Q
        simp [encodePart,NodeGen3.hplenOf,NodeGen3.isLE]
      apply treeRbv_memOk _ base Q kids mem v (by simpa using he) hw rfl _ hhead.1 hhead.2 hL hchild
      change 2<11; decide
    | some old =>
      have he' := he
      simp [encodeTreePart,treeNode] at he'
      have hhead : Q.qhk<2^22 ∧ Q.phk<2^22 := by
        subst Q
        simp [encodePart,NodeGen3.hplenOf,NodeGen3.isLE]
      apply treeRbr_memOk _ base Q old kids mem v (by simpa using he) hw rfl _ hhead.1 hhead.2 hL hchild
      change 1<11; decide

structure ByteMemoryInput (I : UpsInst) (Q : UpsPartI) where
  bytes : ByteInput I Q
  memory : MemOk I Q

/-- Executable value-terminal byte/memory assembly on the same sign-corrected part. -/
def trace_value_byteMemory {source : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert source key v=some run) (hw : source.wf=true)
    (hvterm : valueTerminal source key) (hk : key.length≤2) (hv : v.length<2^24)
    (baseI : UpsInst) {part : TreePart} (hp : part∈run.parts)
    (base : UpsPartI) {Q : UpsPartI} (he : encodeTreePart base part=some Q)
    (hchild : ∀ b∈(child (traceInstance baseI run v) Q).pb,b<256) :
    ByteMemoryInput (traceInstance baseI run v) (withMemorySign (traceInstance baseI run v) Q) :=
  ⟨(trace_value_byteInput hr hw hvterm hk baseI hp base he).withMemorySign,
    trace_value_memOk hr hw hvterm hk hv baseI hp base he hchild⟩
end ZkFormal.NearV3.Render.UpsGen
