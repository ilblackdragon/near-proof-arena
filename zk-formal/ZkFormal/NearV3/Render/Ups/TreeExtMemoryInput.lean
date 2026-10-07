import ZkFormal.NearV3.Render.Ups.TreeExtInput
import ZkFormal.NearV3.Render.Ups.TreeMemoryUp
import ZkFormal.NearV3.Render.Ups.TreeValueMemoryDispatch
import ZkFormal.NearV3.Render.Ups.TreePartBytesBounds

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

/-- Actual extension recursion (including empty-key pass-through) constructs
both byte and memory conditions. Remaining linkage identifies the previously
encoded child and supplies its exact new memory total. -/
def treeExt_byteMemory (I : UpsInst) (base baseChild : UpsPartI) (childKind : UKind)
    (key : List Nat) (childNode : PTrie) (mem cm : Nat) (rest : List Nat) (v : Bytes)
    (run : TreeRun) (Q : UpsPartI)
    (hr : traceUpsert childNode rest v=some run) (hcm : childNode.mem?=some cm)
    (he : encodeTreePart base ⟨if key.isEmpty then .PT else .RDE,
      .ext key childNode mem,qRDE key mem run.output cm,0⟩=some Q)
    (hec : encodeTreePart baseChild ⟨childKind,childNode,run.output,0⟩=some (child I Q))
    (hw : (PTrie.ext key childNode mem).wf=true)
    (hc : I.ci<11) (hq : Q.qhk<2^22) (hp : Q.phk<2^22) (hL : L I<2^24)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16)
    (hm : Q.mB=run.output.memD) (hb : run.output.memD<2^74) :
    ByteMemoryInput I (withMemorySign I Q) := by
  let data := treeExt_byteInput I base key childNode mem cm rest v run Q hr he hw hts hx
  refine ⟨data.withMemorySign,?_⟩
  have hwc : childNode.wf=true := by
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    exact hw.1.1.2
  have hmem : childNode.memD=cm := by simp [PTrie.memD,hcm]
  apply data.native_memOk he hc hq hp hL (encoded_source_byte_bounds hec hwc) (by omega)
  have hkind : (if key.isEmpty then UKind.PT else .RDE)=.RDE ∨
      (if key.isEmpty then UKind.PT else .RDE)=.PT := by split <;> simp
  have he' : encodeTreePart base ⟨if key.isEmpty then .PT else .RDE,
      .ext key childNode mem,qRDE key mem run.output childNode.memD,0⟩=some Q := by simpa [hmem] using he
  have ht := treeRde_memory I base baseChild Q _ childKind key childNode run.output mem
    hkind he' hec hw hm hL
  simpa only [hmem] using ht
end ZkFormal.NearV3.Render.UpsGen
