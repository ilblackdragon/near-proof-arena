import ZkFormal.NearV3.Render.Ups.TreeBranchTerminal
import ZkFormal.NearV3.Render.Node.WinFacts

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near ZkFormal.Near.Render

def terminalBitmap (run : TreeRun) : Nat :=
  match run.terminalSource with
  | .branch _ kids _ => kidBitmap (treeKids kids)
  | _ => 0

def terminalHasVal (run : TreeRun) : Nat :=
  match run.terminalSource with
  | .branch value _ _ => if value.isSome then 1 else 0
  | _ => 0

theorem terminalHasVal_bit (run : TreeRun) : terminalHasVal run≤1 := by
  unfold terminalHasVal
  cases run.terminalSource <;> simp
  split <;> decide

theorem terminalBitmap_bound {run : TreeRun} (hw : run.terminalSource.wf=true) :
    terminalBitmap run<2^16 := by
  unfold terminalBitmap
  cases hn : run.terminalSource with
  | hash => simp
  | leaf => simp
  | ext => simp
  | branch value kids mem =>
    have hw' : (PTrie.branch value kids mem).wf=true := by simpa [hn] using hw
    have hnode : (NodeV3.branch (value.map treeSlot) (treeKids kids) ((u64 mem).map UInt8.toNat)).wf :=
      treeNode_wf hw' rfl
    exact Link.kidBitmap_lt hnode.1

/-- A branch-value insertion reads the actual empty value slot. -/
theorem traceUpsert_absentValue {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (hc : run.terminal=.BV) :
    run.matched=0 ∧ terminalHasVal run=0 := by
  obtain ⟨kids,mem,hs,hm⟩ := (traceUpsert_branchTerminal root key v run hr).1 hc
  exact ⟨hm,by simp [terminalHasVal,hs]⟩

/-- A missing fixed-key branch child clears exactly the bit read by W1 or W2. -/
theorem traceUpsert_absentBitmap {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hc : run.terminal=.BI) :
    run.matched=0 ∧
    (run.splitCursor [0,15]=1 → terminalBitmap run%2=0) ∧
    (run.splitCursor [0,15]=2 → terminalBitmap run/2^15%2=0) := by
  obtain ⟨value,kids,mem,slot,rest,hs,hkey,hnone,hm⟩ :=
    (traceUpsert_branchTerminal root [0,15] v run hr).2 hc
  have habs := (nativeChildAt_none_iff kids slot).mpr hnone
  have hbit : NodeGen.bitOf (kidBitmap (treeKids kids)) slot=0 := by
    rw [NodeGen3.bitOf_kidBitmap]
    simp only [List.getD_eq_getElem?_getD] at habs
    simp [NodeGen3.kbit,habs]
  obtain ⟨d,_,hterm,_⟩ := traceUpsert_keys root [0,15] v run hr
  have hf : FixedSuffix run.terminalKey := by rw [hterm]; exact FixedSuffix.drop (Or.inr (Or.inr rfl)) d
  refine ⟨hm,?_⟩
  rcases hf with hz|hz|hz
  · simp [hkey] at hz
  · rw [hkey] at hz
    obtain ⟨rfl,rfl⟩ := List.cons.inj hz
    simp [terminalBitmap,hs,TreeRun.splitCursor,TreeRun.consumed,hkey,hm]
    simpa [NodeGen.bitOf] using hbit
  · rw [hkey] at hz
    obtain ⟨rfl,rfl⟩ := List.cons.inj hz
    simp [terminalBitmap,hs,TreeRun.splitCursor,TreeRun.consumed,hkey,hm]
    simpa [NodeGen.bitOf] using hbit
end ZkFormal.NearV3.Render.UpsGen
