import ZkFormal.NearV3.Render.Ups.TreeValueMemoryDispatch

namespace LeafTerminalCursorRegression
open NearSpec ZkFormal.NearV3.Render.UpsGen ZkFormal.NearV3.UpsRows

def source : PTrie := .leaf [0,15] (.val []) 0
def result : TreeRun := terminalRun source [0,15] .LP 2 (newLeaf [0,15] [])
  [⟨.RLP,source,newLeaf [0,15] [],0⟩]

example : source.wf=true := by decide
example : traceUpsert source [0,15] []=some result := rfl
example : source.upsert [0,15] []=some result.output := rfl
example (base : ZkFormal.NearV3.Render.UpsInst) :
    (traceInstance base result []).ts=3 ∧
    (traceInstance base result []).ti=2 ∧
    (traceInstance base result []).ci=0 := by
  simp [traceInstance,result,terminalRun,TreeRun.splitCursor,TreeRun.consumed,UCase.ix]

/-- A nonempty prefix before the leaf still ends at the value step. -/
def suffixSource : PTrie := .ext [0] (.leaf [15] (.val []) 0) 0
def suffixInner : TreeRun := terminalRun (.leaf [15] (.val []) 0) [15] .LP 1
  (newLeaf [15] []) [⟨.RLP,.leaf [15] (.val []) 0,newLeaf [15] [],0⟩]
def suffixResult : TreeRun := pushPart suffixInner
  ⟨.RDE,suffixSource,ZkFormal.NearV3.UpsSpec.qRDE [0] 0 suffixInner.output 0,0⟩
example : traceUpsert suffixSource [0,15] []=some suffixResult := rfl
example (base : ZkFormal.NearV3.Render.UpsInst) :
    (traceInstance base suffixResult []).ts=3 ∧ (traceInstance base suffixResult []).ti=1 := by
  simp [traceInstance,suffixResult,suffixInner,pushPart,terminalRun,TreeRun.splitCursor,TreeRun.consumed]
def emptySource : PTrie := .ext [0,15] (.leaf [] (.val []) 0) 0
def emptyInner : TreeRun := terminalRun (.leaf [] (.val []) 0) [] .LP 0
  (newLeaf [] []) [⟨.RLP,.leaf [] (.val []) 0,newLeaf [] [],0⟩]
def emptyResult : TreeRun := pushPart emptyInner
  ⟨.RDE,emptySource,ZkFormal.NearV3.UpsSpec.qRDE [0,15] 0 emptyInner.output 0,0⟩
example : traceUpsert emptySource [0,15] []=some emptyResult := rfl
example (base : ZkFormal.NearV3.Render.UpsInst) :
    (traceInstance base emptyResult []).ts=3 ∧ (traceInstance base emptyResult []).ti=0 := by
  simp [traceInstance,emptyResult,emptyInner,pushPart,terminalRun,TreeRun.splitCursor,TreeRun.consumed]

/-- info: 'ZkFormal.NearV3.Render.UpsGen.trace_value_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.trace_value_end
end LeafTerminalCursorRegression
