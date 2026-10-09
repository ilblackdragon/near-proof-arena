import ZkFormal.NearV3.Render.Ups.NodeMemoryFooter
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near

/-- Reuse the concrete byte constructor's output view. Each actual runtime case
supplies its checked native scalar formula; carry and modular serialization facts
then follow uniformly, without a second output-shape or output-memory bound. -/
theorem ByteInput.native_memOk {I : UpsInst} {base Q : UpsPartI} {part : TreePart}
    (data : ByteInput I Q) (he : encodeTreePart base part=some Q)
    (hc : I.ci<11) (hq : Q.qhk<2^22) (hp : Q.phk<2^22) (hL : L I<2^24)
    (hchild : ∀ b∈(child I Q).pb,b<256) (hm : Q.mB<2^74)
    (hr : RV I (withMemorySign I Q)=(part.output.memD:Int)) : MemOk I (withMemorySign I Q) := by
  have hf := data.output.native_memory he
  refine construct_memOk_bounded I Q data.output data.kind hc hq hp hL
    data.sourceBytes hchild ?_ hm ?_
  · rw [hf]
    intro b hb; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hb; exact x.toNat_lt
  · rw [← withMemorySign_RV,hr,hf,u64_memory_decode]
    omega
def SourceLayout.withMemorySign {I : UpsInst} {Q : UpsPartI} (e : SourceLayout Q) :
    SourceLayout (UpsGen.withMemorySign I Q) := ⟨e.node,e.wf,e.bytes,e.edit⟩

def SourceHeader.withMemorySign {I : UpsInst} {Q : UpsPartI} {e : SourceLayout Q}
    (h : SourceHeader I Q e) : SourceHeader I (UpsGen.withMemorySign I Q) e.withMemorySign :=
  ⟨h.hplen,h.odd,h.prefixNode,h.leaf,h.insertValue⟩

/-- Choosing the honest subtraction sign preserves all ordinary byte semantics. -/
def ByteInput.withMemorySign {I : UpsInst} {Q : UpsPartI} (data : ByteInput I Q) :
    ByteInput I (UpsGen.withMemorySign I Q) where
  output := data.output.withMemorySign
  kind := data.kind
  nochild := data.nochild
  freshPrefix := ⟨data.freshPrefix.terminal,data.freshPrefix.leaf,data.freshPrefix.wrap,data.freshPrefix.pass⟩
  freshValue := ⟨data.freshValue.slot⟩
  splitBitmap := ⟨data.splitBitmap.xbound,data.splitBitmap.slots,data.splitBitmap.distinct⟩
  sourceBytes := data.sourceBytes
  sourceLayout h := (data.sourceLayout h).withMemorySign
  sourceHeader h := ⟨(data.sourceHeader h).val.withMemorySign,(data.sourceHeader h).property.withMemorySign⟩
  movedPrefix h := ⟨(data.movedPrefix h).source.withMemorySign,(data.movedPrefix h).header.withMemorySign,
    (data.movedPrefix h).key,(data.movedPrefix h).leaf,(data.movedPrefix h).prefixNode⟩
  sourceValue ht hv := ⟨(data.sourceValue ht hv).source.withMemorySign,(data.sourceValue ht hv).edit,
    (data.sourceValue ht hv).hplen,(data.sourceValue ht hv).offset⟩
  copyFields := ⟨data.copyFields.fields⟩
end ZkFormal.NearV3.Render.UpsGen
