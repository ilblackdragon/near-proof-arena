import ZkFormal.NearV3.Render.Ups.MemSemantic
import ZkFormal.NearV3.Render.Ups.MemScalars

/-! Assemble honest memory obligations from ordinary scalar arithmetic and serialization.
Sign bits and all intermediate carry ranges are derived internally. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near

def NodeEncoding.withMemorySign {I : UpsInst} {Q : UpsPartI} (e : NodeEncoding Q) :
    NodeEncoding (UpsGen.withMemorySign I Q) :=
  ⟨e.node,e.wf,e.bytes,e.shape,e.ty,e.hplen,e.odd⟩

theorem construct_memOk (I : UpsInst) (Q : UpsPartI) (e : NodeEncoding Q)
    (hk : Q.kind<12) (hc : I.ci<11) (hq : Q.qhk<2^22) (hp : Q.phk<2^22)
    (hL : L I<2^24) (hb : ∀ b∈Q.pb,b<256)
    (hchild : ∀ b∈(child I Q).pb,b<256)
    (hout : ∀ b∈NodeGen3.memOf e.node,b<256)
    (hl : -(131072*256^8)<pfx (X1V I Q) 8)
    (hu : pfx (X1V I Q) 8<131072*256^8)
    (hr : (pfx (EinV I Q) 8+(if pfx (X1V I Q) 8<0 then 0 else pfx (X1V I Q) 8))%256^8=
      (le256 (NodeGen3.memOf e.node):Int)) :
    MemOk I (withMemorySign I Q) := by
  have hn := withMemorySign_bit I Q
  have hs := memory_scalar_sums I (withMemorySign I Q) hk hc hq hp hn hL hb hchild
  apply memOk_of_semantics (e.withMemorySign (I:=I)) hout
    (by rw [withMemorySign_RV]; exact hr) hn hs.1 hs.2
  exact withMemorySign_bound I Q _ hl hu
end ZkFormal.NearV3.Render.UpsGen
