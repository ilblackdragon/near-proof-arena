import ZkFormal.NearV3.Render.Ups.FourWalk
import ZkFormal.NearV3.Render.Ups.NativeWalkPayload
import ZkFormal.NearV3.Render.Ups.NativeWalkMismatch

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Construct the four walk rows before building the native instance. Source/value
record maps remain parameters of the authenticated store allocation. -/
def nativeWalkBase (recordId : PTrie→Nat) (valueId : Slot→Nat) (resolvedId : PTrie→Nat)
    (baseI : UpsInst) (root : PTrie) (run : TreeRun) (v : Bytes) : UpsInst :=
  let I := positionedInstance recordId baseI root run v []
  let target := nativeTerminalTarget valueId resolvedId run (recordId run.terminalSource)
  let walk := fourWalk I (terminalBitmap run) (terminalHasVal run)
    (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target.1 target.2
  {baseI with walk:=walk}

/-- The concrete native walk is locally legal. Authentication of its generated edges
and bitmap against stored node views is a separate cross-table traffic obligation. -/
theorem nativeInstance_walk (recordId : PTrie→Nat) (valueId : Slot→Nat) (resolvedId : PTrie→Nat)
    (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true) (Qs : List UpsPartI) :
    WalkOkU (nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs) := by
  let I := nativeInstance recordId baseI root run v Qs
  let target := nativeTerminalTarget valueId resolvedId run (recordId run.terminalSource)
  change WalkOkU (withFourWalk I (terminalBitmap run) (terminalHasVal run)
    (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target.1 target.2)
  have hb := traceInstance_bounds hr hw baseI
  have he := traceInstance_terminalCases hr baseI
  apply fourWalk_ok I _ _ _ _ _ _ hb.1 ⟨hb.2.2.1,hb.2.2.2.1⟩ hb.2.1
    (traceUpsert_walk_geometry hr) he.1 he.2
  · intro hcase
    change run.terminal.ix=2 ∨ run.terminal.ix=3 at hcase
    have hc : run.terminal=.BV ∨ run.terminal=.BI := by
      cases ht : run.terminal <;> simp_all [UCase.ix]
    change run.matched=0
    rcases hc with hc|hc
    · exact (traceUpsert_absentValue hr hc).1
    · exact (traceUpsert_absentBitmap hr hc).1
  · exact terminalBitmap_bound (traceUpsert_sources root [0,15] v run hw hr).1
  · exact terminalHasVal_bit run
  · intro hcase
    have hc : run.terminal=.BV := by
      change run.terminal.ix=2 at hcase
      cases ht : run.terminal <;> simp_all [UCase.ix]
    exact (traceUpsert_absentValue hr hc).2
  · intro hcase hts
    have hc : run.terminal=.BI := by
      change run.terminal.ix=3 at hcase
      cases ht : run.terminal <;> simp_all [UCase.ix]
    exact (traceUpsert_absentBitmap hr hc).2.1 hts
  · intro hcase hts
    have hc : run.terminal=.BI := by
      change run.terminal.ix=3 at hcase
      cases ht : run.terminal <;> simp_all [UCase.ix]
    exact (traceUpsert_absentBitmap hr hc).2.2 hts
  · intro hc
    exact traceInstance_absentSymbol baseI hr hw hc
  · exact nativePathEdgeKind_bound run 0
  · exact nativePathEdgeKind_bound run _
/-- Native execution now constructs every instance condition, including the walk.
Only value-size bounds and the ordinary executable part encoding remain as inputs. -/
theorem nativeInstance_constructed_ok (recordId : PTrie→Nat) (valueId : Slot→Nat)
    (resolvedId : PTrie→Nat) (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (hv : 1≤v.length) (hvsmall : v.length<2^24) (base : Nat→UpsPartI)
    {Qs : List UpsPartI} (he : encodeNativeParts recordId root run base=some Qs) :
    InstOk (nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs) :=
  nativeInstance_semantic_ok recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
    hr hw hv hvsmall base he (nativeInstance_walk recordId valueId resolvedId baseI hr hw Qs)

/-- The native part encoder succeeds and yields a locally legal instance without a
caller-supplied walk, byte family, or constraint-evaluation premise. -/
theorem nativeInstance_constructed_exists (recordId : PTrie→Nat) (valueId : Slot→Nat)
    (resolvedId : PTrie→Nat) (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (hv : 1≤v.length) (hvsmall : v.length<2^24) (base : Nat→UpsPartI) :
    ∃ Qs, encodeNativeParts recordId root run base=some Qs ∧
      InstOk (nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
        root run v Qs) := by
  obtain ⟨Qs,he,_⟩ := encodeNativeParts_total recordId hr base
  exact ⟨Qs,he,nativeInstance_constructed_ok recordId valueId resolvedId baseI hr hw hv hvsmall base he⟩
end ZkFormal.NearV3.Render.UpsGen
