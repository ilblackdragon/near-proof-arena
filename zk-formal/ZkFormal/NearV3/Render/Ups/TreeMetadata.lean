import ZkFormal.NearV3.Render.Ups.TreeKeys
import ZkFormal.NearV3.Render.Ups.TreeSources
import ZkFormal.NearV3.Render.Ups.TreeEncodingTotal

/-! Terminal case, cursor and divergent nibble are computed from the actual trace.
Store IDs and per-part memory/window metadata remain allocator responsibilities. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

def TreeRun.splitNibble (run : TreeRun) : Nat :=
  match run.terminalSource with
  | .leaf key _ _ | .ext key _ _ => key.getD run.matched 0
  | _ => 0

/-- Fill the trace-derived instance fields while retaining the allocator's other fields. -/
def traceInstance (base : UpsInst) (run : TreeRun) (v : Bytes) : UpsInst :=
  {base with
    ci := run.terminal.ix
    ti := run.matched
    ts := run.splitCursor [0,15]
    x := run.splitNibble
    v := v.map UInt8.toNat}

theorem nibble_getD_lt : ∀ (key : List Nat) (n : Nat), nibblesOk key=true → key.getD n 0<16
  | [], _, _ => by simp
  | x::xs, 0, h => by simpa using (nibblesOk_cons.mp h).1
  | x::xs, n+1, h => by simpa using nibble_getD_lt xs n (nibblesOk_cons.mp h).2

theorem splitNibble_lt {run : TreeRun} (hw : run.terminalSource.wf=true) : run.splitNibble<16 := by
  unfold TreeRun.splitNibble
  cases he : run.terminalSource with
  | hash h => change 0<16; decide
  | branch bv kids mem => change 0<16; decide
  | leaf key value mem =>
    rw [he] at hw
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    exact nibble_getD_lt key run.matched hw.1.1.1
  | ext key child mem =>
    rw [he] at hw
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    exact nibble_getD_lt key run.matched hw.1.1.1

/-- All case/cursor/nibble bounds are consequences of native execution on the fixed key. -/
theorem traceInstance_bounds {t : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t [0,15] v=some run) (hw : t.wf=true) (base : UpsInst) :
    (traceInstance base run v).ci<11 ∧ (traceInstance base run v).ti<3 ∧
    1≤(traceInstance base run v).ts ∧ (traceInstance base run v).ts≤3 ∧
    (traceInstance base run v).x<16 := by
  have hk := trace_fixedKey_bounds hr
  have hs := traceUpsert_sources t [0,15] v run hw hr
  have hx := splitNibble_lt hs.1
  have hc : run.terminal.ix<11 := by cases run.terminal <;> decide
  exact ⟨hc,by simp only [traceInstance]; omega,hk.2.2.1,hk.2.2.2,hx⟩

/-- The executable encoded sequence inherits its runtime plan and trace-derived metadata bounds. -/
theorem upsert_metadata_witness {t result : PTrie} {v : Bytes}
    (hu : t.upsert [0,15] v=some result) (hw : t.wf=true)
    (base : UpsInst) (parts : Nat → UpsPartI) :
    ∃ run Qs, traceUpsert t [0,15] v=some run ∧ run.output=result ∧ run.Planned ∧
      encodeTreeParts parts 0 run.parts=some Qs ∧
      Qs.map UpsPartI.kind=run.parts.map (fun p => p.kind.ix) ∧ Qs.length=run.parts.length ∧
      (traceInstance base run v).ci<11 ∧ (traceInstance base run v).ti<3 ∧
      1≤(traceInstance base run v).ts ∧ (traceInstance base run v).ts≤3 ∧
      (traceInstance base run v).x<16 := by
  obtain ⟨run,Qs,hr,ho,hp,hQ,hk,hl⟩ := upsert_encoded_witness hu parts
  exact ⟨run,Qs,hr,ho,hp,hQ,hk,hl,traceInstance_bounds hr hw base⟩
end ZkFormal.NearV3.Render.UpsGen
