import ZkFormal.NearV3.Render.Ups.TreeExistingTrace
import ZkFormal.NearV3.Render.Ups.TreeExtMemoryInput

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Existing-child branch recursion uses the concrete witness returned by
traceKids_existing, retaining exact new memory while reading old serialized memory. -/
def treeRdb_byteMemory (I : UpsInst) (base baseChild : UpsPartI) (childKind : UKind)
    (value : Option Slot) (kids : Kids) (mem : Nat) (key : List Nat) (v : Bytes)
    (run : KidsRun) (Q : UpsPartI)
    (hr : traceKids (.branch value kids mem) (edgeSlot base.sd::key) kids (edgeSlot base.sd) key v=some run)
    (hi : run.inserted=false) (e : ExistingChild run key v)
    (he : encodeTreePart base ⟨.RDB,.branch value kids mem,
      .branch value run.output (mem+run.newMem-run.oldMem),edgeSlot base.sd⟩=some Q)
    (hec : encodeTreePart baseChild ⟨childKind,e.node,run.inner.output,0⟩=some (child I Q))
    (hw : (PTrie.branch value kids mem).wf=true) (sd : base.sd=0 ∨ base.sd=1)
    (hc : I.ci<11) (hq : Q.qhk<2^22) (hp : Q.phk<2^22) (hL : L I<2^24)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16)
    (hm : Q.mB=run.inner.output.memD) (hb : run.inner.output.memD<2^74) :
    ByteMemoryInput I (withMemorySign I Q) := by
  let data := treeRdb_byteInput I base value kids mem key v run Q hr hi he hw sd hts hx
  refine ⟨data.withMemorySign,?_⟩
  apply data.native_memOk he hc hq hp hL (encoded_source_byte_bounds hec e.wf) (by omega)
  have he' : encodeTreePart base ⟨.RDB,.branch value kids mem,
      .branch value run.output (mem+run.inner.output.memD-e.node.memD),edgeSlot base.sd⟩=some Q := by
    simpa only [e.newMem,e.oldMem] using he
  have ht := treeRdb_memory I base baseChild Q childKind value kids run.output e.node run.inner.output mem
    (edgeSlot base.sd) he' hec hw e.wf hm hL
  change RV I (withMemorySign I Q)=((mem+run.newMem-run.oldMem:Nat):Int)
  simpa only [e.newMem,e.oldMem] using ht
end ZkFormal.NearV3.Render.UpsGen
