import ZkFormal.NearV3.Render.Ups.TreePrefixInput
import ZkFormal.NearV3.Render.Ups.FixedSuffix

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec

@[simp] theorem traceInstance_pushPart (base : UpsInst) (run : TreeRun) (part : TreePart) (v : Bytes) :
    traceInstance base (pushPart run part) v=traceInstance base run v := rfl

@[simp] theorem traceInstance_wrapRun (base : UpsInst) (source : PTrie) (path : List Nat)
    (run : TreeRun) (v : Bytes) :
    traceInstance base (wrapRun source path run) v=traceInstance base run v := by cases path <;> rfl

/-- Add the native common-prefix wrapper after proving the inner split parts. -/
theorem wrapRun_byteInput (I : UpsInst) (source : PTrie) (path : List Nat) (run : TreeRun)
    (hw : source.wf=true) (hn : isNode run.output=true)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16)
    (hp : path=([0,15].drop (I.ts-1-I.ti)).take I.ti)
    (hwrap : path≠[] → I.ts=2 ∧ I.ti=1 ∨ I.ts=3 ∧ I.ti=1 ∨ I.ts=3 ∧ I.ti=2)
    (hinner : ∀ part∈run.parts,∀ (base Q : UpsPartI),encodeTreePart base part=some Q → Nonempty (ByteInput I Q)) :
    ∀ part∈(wrapRun source path run).parts,∀ (base Q : UpsPartI),
      encodeTreePart base part=some Q → Nonempty (ByteInput I Q) := by
  cases path with
  | nil => exact hinner
  | cons p ps =>
    intro part hpart base Q he
    simp only [wrapRun,pushPart,List.mem_append,List.mem_singleton] at hpart
    rcases hpart with hpart|rfl
    · exact hinner part hpart base Q he
    · have he' : encodeTreePart base ⟨.WEX,source,
          .ext (([0,15].drop (I.ts-1-I.ti)).take I.ti) run.output
            (extOwnMem (([0,15].drop (I.ts-1-I.ti)).take I.ti)+run.output.memD),0⟩=some Q := by
        simpa only [wrapExt,hp] using he
      exact ⟨treeWex_byteInput I base source run.output Q he' hw hn hts hx (hwrap (by simp))⟩
end ZkFormal.NearV3.Render.UpsGen
