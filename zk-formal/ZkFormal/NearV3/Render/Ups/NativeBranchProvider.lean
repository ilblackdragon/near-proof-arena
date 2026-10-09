import ZkFormal.NearV3.Render.Ups.NativePathNode

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

/-- Native indexed branch children provide descent edges under the executable annotation. -/
theorem nativePathNode_child_edge (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat)
    (n slot : Nat) (s : NodeS3) (value : Option Slot) (kids : Kids) (mem : Nat)
    (child : PTrie) (cm : Nat) (hc : nativeChildAt kids slot=some child)
    (hm : child.mem?=some cm)
    (hv : nativePathNode recordId resolvedId valueId (.branch value kids mem)=some s.v) :
    [n,0,slot,resolvedId child,0,EK_DOWN]∈edgesOf3 n s := by
  have hs : s.v=.branch (value.map (nativeValueSlot valueId))
      (nativeWalkKids recordId resolvedId kids) ((u64 mem).map UInt8.toNat) := by
    simpa only [nativePathNode,Option.some.injEq] using hv.symm
  have hk := nativeWalkKids_get recordId resolvedId kids slot child hc
  cases child with
  | hash => simp [PTrie.mem?] at hm
  | leaf key value mem | ext key child mem | branch value kids mem =>
    exact branch_child_edge n slot _ _ _ s _ _ _ _ _ hs hk

theorem fourWalk_terminal_bitmap (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (ht : 1≤I.ts ∧ I.ts≤3) :
    (step (withFourWalk I bm hv ek1 ek2 target targetPos) I.ts).bm=bm ∧
    (step (withFourWalk I bm hv ek1 ek2 target targetPos) I.ts).hv=hv := by
  rcases (show I.ts=1 ∨ I.ts=2 ∨ I.ts=3 by omega) with ht|ht|ht <;>
    simp [step,withFourWalk,fourWalk,ht]

/-- The generated absent-branch lookup uses the provider node's actual bitmap/value bit. -/
theorem nativeInstance_branch_bitmap (recordId : PTrie→Nat) (valueId : Slot→Nat)
    (resolvedId : PTrie→Nat) (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hc : run.terminal=.BV ∨ run.terminal=.BI)
    (Qs : List UpsPartI) (s : NodeS3)
    (hnode : nativePathNode recordId resolvedId valueId run.terminalSource=some s.v) :
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs
    s.v.bmap=some ((step I I.ts).bm,(step I I.ts).hv) := by
  dsimp only
  let I := nativeInstance recordId baseI root run v Qs
  let target := nativeTerminalTarget valueId resolvedId run (recordId run.terminalSource)
  have hb := trace_fixedKey_bounds hr
  have ht : 1≤I.ts ∧ I.ts≤3 := ⟨hb.2.2.1,hb.2.2.2⟩
  change s.v.bmap=some (
    (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
      (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target.1 target.2) I.ts).bm,
    (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
      (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target.1 target.2) I.ts).hv)
  have hbits := fourWalk_terminal_bitmap I (terminalBitmap run) (terminalHasVal run)
    (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target.1 target.2 ht
  rw [hbits.1,hbits.2]
  have hbranch := traceUpsert_branchTerminal root [0,15] v run hr
  have hs : ∃ value kids mem,run.terminalSource=.branch value kids mem := by
    rcases hc with hc|hc
    · obtain ⟨kids,mem,hs,_⟩ := hbranch.1 hc
      exact ⟨none,kids,mem,hs⟩
    · obtain ⟨value,kids,mem,slot,rest,hs,_⟩ := hbranch.2 hc
      exact ⟨value,kids,mem,hs⟩
  obtain ⟨value,kids,mem,hs⟩ := hs
  have hv : s.v=.branch (value.map (nativeValueSlot valueId))
      (nativeWalkKids recordId resolvedId kids) ((u64 mem).map UInt8.toNat) := by
    simpa only [hs,nativePathNode,Option.some.injEq] using hnode.symm
  simp [hv,NodeV3.bmap,terminalBitmap,terminalHasVal,hs,nativeWalkKids_bitmap]
end ZkFormal.NearV3.Render.UpsGen
