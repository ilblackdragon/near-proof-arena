import ZkFormal.NearV3.Render.Ups.TreeMetadata
import ZkFormal.NearV3.Render.Ups.TreeValueInput

/-! Checked runtime dispatch for leaf replacement and branch value insertion/replacement.
The predicates describe native constructors and keys, not polynomial evaluations. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

def valueTerminal (source : PTrie) (key : List Nat) : Prop :=
  match source with
  | .leaf oldKey _ _ => oldKey=key
  | .branch _ _ _ => key=[]
  | _ => False

/-- Value-terminal execution dispatches directly to its proved byte constructor. -/
def trace_value_byteInput {source : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert source key v=some run) (hw : source.wf=true)
    (hvterm : valueTerminal source key) (hk : key.length≤2)
    (baseI : UpsInst) {part : TreePart} (hp : part∈run.parts)
    (base : UpsPartI) {Q : UpsPartI} (he : encodeTreePart base part=some Q) :
    ByteInput (traceInstance baseI run v) Q := by
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
    apply treeRlp_byteInput _ base key old mem v Q he hw rfl
    · simp only [traceInstance,TreeRun.splitCursor,TreeRun.consumed,terminalRun,List.length_cons,List.length_nil]
      omega
    · have hsrc : (terminalRun (.leaf key old mem) key .LP key.length (newLeaf key v)
          [⟨.RLP,.leaf key old mem,newLeaf key v,0⟩]).terminalSource.wf=true := hw
      exact splitNibble_lt hsrc
  | branch old kids mem =>
    have hkey : key=[] := hvterm
    subst key
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    simp only [terminalRun,List.mem_singleton] at hp
    subst part
    cases old with
    | none =>
      apply treeRbv_byteInput _ base kids mem v Q (by simpa using he) hw rfl
      · change 1≤3 ∧ 3≤3; decide
      · change 0<16; decide
    | some old =>
      apply treeRbr_byteInput _ base old kids mem v Q (by simpa using he) hw rfl
      · change 1≤3 ∧ 3≤3; decide
      · change 0<16; decide
/-- Existing values are reached at the END symbol, after all remaining leaf key
nibbles have been consumed. -/
theorem trace_value_end {source : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert source key v=some run) (ht : valueTerminal source key)
    (hk : key.length≤2) (base : UpsInst) : (traceInstance base run v).ts=3 := by
  cases source with
  | hash => simp [valueTerminal] at ht
  | ext => simp [valueTerminal] at ht
  | leaf oldKey old mem =>
    have he : oldKey=key := ht
    subst oldKey
    simp only [traceUpsert,ite_true,Option.some.injEq] at hr
    subst run
    simp [traceInstance,terminalRun,TreeRun.splitCursor,TreeRun.consumed]
    omega
  | branch old kids mem =>
    have he : key=[] := ht
    subst key
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    rfl

end ZkFormal.NearV3.Render.UpsGen
