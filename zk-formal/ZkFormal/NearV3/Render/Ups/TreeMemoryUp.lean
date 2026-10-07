import ZkFormal.NearV3.Render.Ups.MemUpScalars
import ZkFormal.NearV3.Render.Ups.MemTotalBounds

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

/-- An extension ancestor reads the authenticated old child while retaining the
new child's exact scalar, which may exceed its serialized u64 value. -/
theorem treeRde_memory (I : UpsInst) (base baseChild Q : UpsPartI)
    (kind childKind : UKind) (key : List Nat) (oldChild newChild : PTrie) (mem : Nat)
    (hk : kind=.RDE ∨ kind=.PT)
    (he : encodeTreePart base ⟨kind,.ext key oldChild mem,qRDE key mem newChild oldChild.memD,0⟩=some Q)
    (hc : encodeTreePart baseChild ⟨childKind,oldChild,newChild,0⟩=some (child I Q))
    (hw : (PTrie.ext key oldChild mem).wf=true)
    (hm : Q.mB=newChild.memD) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((qRDE key mem newChild oldChild.memD).memD:Int) := by
  have hparent := encoded_source_memory_exact he hw
  change pfx (memRb Q) 8=(mem:Int) at hparent
  have hwo : oldChild.wf=true := by
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    exact hw.1.1.2
  have hchild := encoded_child_memory hc hwo
  have hkind : Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=11 := by
    have hh := encodeTreePart_kind he
    rcases hk with rfl|rfl <;> simp_all [UKind.ix]
  rw [up_memory_scalar I Q hL hkind mem oldChild.memD hparent hchild,hm]
  rfl

/-- Branch ancestors propagate the same exact child-memory delta. Child-slot
replacement itself is handled by the ordinary runtime/node-view constructor. -/
theorem treeRdb_memory (I : UpsInst) (base baseChild Q : UpsPartI)
    (childKind : UKind) (value : Option Slot) (oldKids newKids : Kids)
    (oldChild newChild : PTrie) (mem slot : Nat)
    (he : encodeTreePart base ⟨.RDB,.branch value oldKids mem,
      .branch value newKids (mem+newChild.memD-oldChild.memD),slot⟩=some Q)
    (hc : encodeTreePart baseChild ⟨childKind,oldChild,newChild,0⟩=some (child I Q))
    (hw : (PTrie.branch value oldKids mem).wf=true) (hwo : oldChild.wf=true)
    (hm : Q.mB=newChild.memD) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((mem+newChild.memD-oldChild.memD:Nat):Int) := by
  have hparent := encoded_source_memory_exact he hw
  change pfx (memRb Q) 8=(mem:Int) at hparent
  have hchild := encoded_child_memory hc hwo
  have hkind : Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=11 := by
    have hh := encodeTreePart_kind he
    exact Or.inl hh
  rw [up_memory_scalar I Q hL hkind mem oldChild.memD hparent hchild,hm]
end ZkFormal.NearV3.Render.UpsGen
