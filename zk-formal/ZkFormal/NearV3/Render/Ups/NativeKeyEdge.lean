import ZkFormal.NearV3.Render.Ups.NativeKeyNode

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

theorem fourWalk_absent_terminal (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (ht : 1≤I.ts ∧ I.ts≤3) (hc : 4≤I.ci) :
    (step (withFourWalk I bm hv ek1 ek2 target targetPos) I.ts).e=
      [I.N.getD I.D 0,I.ti,(if I.ci=4 then SYM_END else I.x),target,targetPos,
        if I.ci=4 then EK_LEND else EK_KEY] := by
  have h01 : ¬I.ci≤1 := by omega
  rcases (show I.ts=1 ∨ I.ts=2 ∨ I.ts=3 by omega) with ht|ht|ht <;>
    simp [step,withFourWalk,fourWalk,ht,terminalSymbol,hc,h01]

/-- Every constructed absent-key terminal edge is supplied by the executable source
node annotation, including extension transitions to resolved revealed children. -/
theorem nativeInstance_key_edge (recordId : PTrie→Nat) (valueId : Slot→Nat)
    (resolvedId : PTrie→Nat) (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (hc : 4≤run.terminal.ix) (Qs : List UpsPartI) (s : NodeS3)
    (hnode : nativeKeyNode recordId resolvedId valueId run.terminalSource=some s.v) :
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs
    (step I I.ts).e∈edgesOf3 (recordId run.terminalSource) s := by
  dsimp only
  let I := nativeInstance recordId baseI root run v Qs
  let target := nativeTerminalTarget valueId resolvedId run (recordId run.terminalSource)
  have hb := traceInstance_bounds hr hw baseI
  have ht : 1≤I.ts ∧ I.ts≤3 := ⟨hb.2.2.1,hb.2.2.2.1⟩
  change (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
    (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0))
    target.1 target.2) I.ts).e∈edgesOf3 (recordId run.terminalSource) s
  rw [fourWalk_absent_terminal I _ _ _ _ _ _ ht hc]
  change [(sourceLevelIds recordId run).getD (descentCount run.parts) 0,run.matched,
    (if run.terminal.ix=4 then SYM_END else run.splitNibble),target.1,target.2,
    if run.terminal.ix=4 then EK_LEND else EK_KEY]∈edgesOf3 (recordId run.terminalSource) s
  rw [sourceLevelIds_terminal]
  have hk := traceUpsert_keyTerminal root [0,15] v run hr
  cases hcs : run.terminal with
  | LP | BR | BV | BI => simp [hcs,UCase.ix] at hc
  | LSa =>
    simp only [KeyTerminal,hcs] at hk
    obtain ⟨key,slot,mem,hs,hi⟩ := hk
    have hv : s.v=.leaf key (nativeValueSlot valueId slot) ((u64 mem).map UInt8.toNat) := by
      simpa only [hs,nativeKeyNode,Option.some.injEq] using hnode.symm
    have he := leaf_end_edge (recordId run.terminalSource) s key _ _ hv
    simpa [target,nativeTerminalTarget,hcs,UCase.ix,hs,hi] using he
  | LSb | LSc =>
    simp only [KeyTerminal,hcs] at hk
    obtain ⟨key,slot,mem,hs,hi⟩ := hk
    have hv : s.v=.leaf key (nativeValueSlot valueId slot) ((u64 mem).map UInt8.toNat) := by
      simpa only [hs,nativeKeyNode,Option.some.injEq] using hnode.symm
    have he := leaf_key_edge (recordId run.terminalSource) run.matched s key _ _ hv hi
    simpa [target,nativeTerminalTarget,hcs,UCase.ix,hs,TreeRun.splitNibble] using he
  | ESl0 | ESl1 | ESn0 | ESn1 =>
    simp only [KeyTerminal,hcs] at hk
    obtain ⟨key,child,mem,hs,hi⟩ := hk
    have hv : s.v=.ext key (nativeWalkKid recordId resolvedId child) ((u64 mem).map UInt8.toNat) := by
      simpa only [hs,nativeKeyNode,Option.some.injEq] using hnode.symm
    have he := ext_key_edge (recordId run.terminalSource) run.matched s key _ _ hv hi
    have htarget : target=extKeyTarget (recordId run.terminalSource) run.matched key
        (nativeWalkKid recordId resolvedId child) := by
      cases child <;> simp [target,nativeTerminalTarget,hcs,hs,extKeyTarget,nativeWalkKid]
    rw [htarget]
    simpa [hcs,UCase.ix,hs,TreeRun.splitNibble] using he
end ZkFormal.NearV3.Render.UpsGen
