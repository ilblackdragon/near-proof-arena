import ZkFormal.NearV3.Render.Ups.NativeWalkConstruction
import ZkFormal.NearV3.Render.Ups.TreeValueTerminal
import ZkFormal.NearV3.Render.Ups.BranchWalkEdges

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

/-- The ordinary value-slot portion of an allocated node view. This records source
shape and the allocator's value ID, with no edge-membership or AIR premise. -/
def NativeValueView (valueId : Slot→Nat) (source : PTrie) (view : NodeV3) : Prop :=
  match source with
  | .leaf key (.val bytes) _ =>
    ∃ lenB pre post mem vlen written,
      view=.leaf key (.val lenB (valueId (.val bytes)) vlen pre post written) mem
  | .branch (some (.val bytes)) _ _ =>
    ∃ lenB pre post mem vlen written kids,
      view=.branch (some (.val lenB (valueId (.val bytes)) vlen pre post written)) kids mem
  | _ => True

theorem fourWalk_value_terminal (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (ht : I.ts=3) (hc : I.ci≤1) :
    (step (withFourWalk I bm hv ek1 ek2 target targetPos) 3).e=
      [I.N.getD I.D 0,I.ti,SYM_END,target,targetPos,EK_VAL] := by
  have h4 : ¬4≤I.ci := by omega
  simp [step,withFourWalk,fourWalk,ht,terminalSymbol,h4,hc,wsym]

/-- A native present-value terminal's generated edge is supplied by its allocated
source view. Actual write-key read determinacy and ordinary value-ID allocation are
explicit semantic inputs; neither the edge nor a constraint evaluation is assumed. -/
theorem nativeInstance_value_edge (recordId : PTrie→Nat) (valueId : Slot→Nat)
    (resolvedId : PTrie→Nat) (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run)
    (hfind : root.find [0,15]≠none) (hc : run.terminal=.LP ∨ run.terminal=.BR)
    (Qs : List UpsPartI) (s : NodeS3) (hview : NativeValueView valueId run.terminalSource s.v) :
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs
    (step I I.ts).e∈edgesOf3 (recordId run.terminalSource) s := by
  dsimp only
  let I := nativeInstance recordId baseI root run v Qs
  let target := nativeTerminalTarget valueId resolvedId run (recordId run.terminalSource)
  have hci : I.ci≤1 := by rcases hc with hc|hc <;> change run.terminal.ix≤1 <;> rw [hc] <;> decide
  have ht : I.ts=3 := by
    have hn := (traceInstance_terminalCases hr baseI).2
    by_cases h : I.ts=3
    · exact h
    · have hn' : I.ci=3 ∨ I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10 := hn h
      omega
  change (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
    (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0))
    target.1 target.2) I.ts).e∈edgesOf3 (recordId run.terminalSource) s
  rw [ht,fourWalk_value_terminal I _ _ _ _ _ _ ht hci]
  change [(sourceLevelIds recordId run).getD (descentCount run.parts) 0,run.matched,SYM_END,
    target.1,target.2,EK_VAL]∈edgesOf3 (recordId run.terminalSource) s
  rw [sourceLevelIds_terminal]
  have hv := traceUpsert_valueTerminal root [0,15] v run hr hfind
  rcases hc with hc|hc
  · obtain ⟨key,bytes,mem,hs,hi⟩ := hv.1 hc
    rw [hs] at hview
    obtain ⟨lenB,pre,post,memB,vlen,written,hview⟩ := hview
    have htarget : target=(valueId (.val bytes),0) := by simp [target,nativeTerminalTarget,hc,hs]
    rw [hi,htarget]
    exact leaf_value_edge _ s key lenB pre post memB _ vlen written hview
  · obtain ⟨bytes,kids,mem,hs,hi⟩ := hv.2 hc
    rw [hs] at hview
    obtain ⟨lenB,pre,post,memB,vlen,written,kidsV,hview⟩ := hview
    have htarget : target=(valueId (.val bytes),0) := by simp [target,nativeTerminalTarget,hc,hs]
    rw [hi,htarget]
    exact branch_value_edge _ s lenB pre post memB _ vlen written kidsV hview
end ZkFormal.NearV3.Render.UpsGen
