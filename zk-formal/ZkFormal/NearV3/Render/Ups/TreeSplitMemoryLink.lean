import ZkFormal.NearV3.Render.Ups.TreeExtSplitDispatch
import ZkFormal.NearV3.Render.Ups.TreeMemorySplit
import ZkFormal.NearV3.Render.Ups.TreeMemoryPrefix

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- The native memory passed from a moved split child or the branch beneath a wrapper.
The value is immaterial for split cases without a moved child. -/
def splitChildMemory (matched : Nat) (part : TreePart) : Nat :=
  match part.kind,part.source,part.output with
  | .WEX,_,.ext _ child _ => child.memD
  | .SPB,.leaf key value _,_ => leafMem (key.drop (matched+1)) value.len
  | .SPB,.ext key _ mem,_ => extOwnMem (key.drop (matched+1))+(mem-extOwnMem key)
  | _,_,_ => 0

/-- A wrapper reads exactly the preceding native branch memory. -/
theorem split_wrap_memory (baseI : UpsInst) (source : PTrie) (key path : List Nat)
    (cs : UCase) (n : Nat) (result : PTrie) (parts : List TreePart) (v : Bytes)
    (hL : v.length<2^24)
    (hi : ∀ part∈parts,∀ base Q,encodeTreePart base part=some Q →
      Q.mB=splitChildMemory n part →
      RV (splitInstance baseI source key cs n v)
        (withMemorySign (splitInstance baseI source key cs n v) Q)=(part.output.memD:Int)) :
    ∀ part∈(wrapRun source path (terminalRun source key cs n result parts)).parts,
      ∀ base Q,encodeTreePart base part=some Q → Q.mB=splitChildMemory n part →
      RV (traceInstance baseI (wrapRun source path (terminalRun source key cs n result parts)) v)
        (withMemorySign (traceInstance baseI (wrapRun source path
          (terminalRun source key cs n result parts)) v) Q)=(part.output.memD:Int) := by
  rw [traceInstance_wrapRun]
  cases path with
  | nil => exact hi
  | cons x xs =>
    intro part hp base Q he hm
    simp only [wrapRun,pushPart,terminalRun,List.mem_append,List.mem_singleton] at hp
    rcases hp with hp|rfl
    · exact hi part hp base Q he hm
    · exact treeWex_memory _ base Q source result (x::xs) he hm (by simpa [L,traceInstance] using hL)
end ZkFormal.NearV3.Render.UpsGen
