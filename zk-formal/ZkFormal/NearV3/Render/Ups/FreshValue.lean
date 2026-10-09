import ZkFormal.NearV3.Render.Ups.NodeHeaderBytes
import ZkFormal.NearV3.Extract.Ups.PartBytes

/-! Fresh value slots carry the ordinary little-endian length of the inserted value. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render
open NodeGen (F)

structure FreshValue (I : UpsInst) (Q : UpsPartI) (e : NodeEncoding Q) : Prop where
  slot : (Q.ty=0 ∨ Q.ty=3) → VcpB I Q = false → ∃ sv, NodeGen3.slotOf e.node = some sv ∧
    sv.lenB = (NearSpec.u32 (L I)).map UInt8.toNat

theorem FreshValue.length_byte {I : UpsInst} {Q : UpsPartI} {e : NodeEncoding Q}
    (h : FreshValue I Q e) (hL : L I < 2^24) {p : Nat} (hp : p < Q.q.length)
    (hs : (fieldAt Q.shape p).1=4) (hc : VcpB I Q=false) :
    (Q.q.getD p 0 : Int) = Lb I (fieldAt Q.shape p).2.1 := by
  obtain ⟨f,hf,hstate,hidx,hbyte⟩ := e.byte_field hp
  have hvlen : f = .vlen := by
    cases f <;> simp [F.state,Node.sTAG,Node.sHPL,Node.sHPF,Node.sKEY,Node.sVLEN,Node.sVH,
      Node.sBM,Node.sCH,Node.sMEM,hs] at hstate ⊢
  subst f
  have ht : Q.ty=0 ∨ Q.ty=3 := by
    have hh := (NodeGen3.kind_facts hf).2.1 (Or.inl rfl)
    rw [e.ty]
    cases hn : e.node with
    | leaf => simp [nodeTypeCode]
    | ext => simp [hn,NodeGen3.typeOf] at hh
    | branch sv kids mem =>
      cases sv <;> simp_all [NodeGen3.typeOf,nodeTypeCode]
  obtain ⟨sv,hsv,hlen⟩ := h.slot ht hc
  simp only [F.len] at hidx
  rw [hbyte]
  simp only [NodeGen3.fbytes,hsv,Option.map_some,Option.getD_some,hlen,UpsRows.toNats_u32]
  have h2 : L I / 65536 < 256 := by omega
  have h3 : L I / 16777216=0 := by omega
  rcases (show (fieldAt Q.shape p).2.1=0 ∨ (fieldAt Q.shape p).2.1=1 ∨
      (fieldAt Q.shape p).2.1=2 ∨ (fieldAt Q.shape p).2.1=3 by omega)
    with hi | hi | hi | hi <;> rw [hi] <;> simp [Lb,h3,Nat.mod_eq_of_lt h2]

end ZkFormal.NearV3.Render.UpsGen
