import ZkFormal.NearV3.Render.Ups.MovedPrefixMath
import ZkFormal.NearV3.Render.Ups.SourceHeader
import ZkFormal.NearV3.Render.Ups.PrefixPosition
import ZkFormal.NearV3.Render.Ups.FreshPrefix

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

/-- A moved leaf/extension removes the consumed nibble prefix, preserving its node kind. -/
structure MovedPrefix (I : UpsInst) (Q : UpsPartI) (dst : NodeEncoding Q) where
  source : SourceLayout Q
  header : SourceHeader I Q source
  key : NodeGen3.keyOf dst.node = (NodeGen3.keyOf source.node).drop (I.ti+1)
  leaf : NodeGen3.isLeaf dst.node = NodeGen3.isLeaf source.node
  prefixNode : NodeGen3.isLE dst.node=true

theorem SourceHeader.key_byte {I : UpsInst} {Q : UpsPartI} {e : SourceLayout Q}
    (h : SourceHeader I Q e) (hk : Q.kind=6 ∨ Q.kind=7 ∨ XcpB I Q=true)
    {j : Nat} (hj : j<Q.phk) : Q.pb.getD (5+j) 0=
      (hpN (NodeGen3.keyOf e.node) (NodeGen3.isLeaf e.node)).getD j 0 := by
  have hs := h.prefixNode hk
  have hl : j < (hpN (NodeGen3.keyOf e.node) (NodeGen3.isLeaf e.node)).length := by
    rw [NodeGen3.hpN_len]
    rw [h.hplen] at hj
    simpa [NodeGen3.hplenOf,hs] using hj
  rw [e.bytes]
  cases hn : e.node with
  | leaf =>
    simp only [hn,NodeGen3.keyOf,NodeGen3.isLeaf] at hl
    simp [NodeV3.ser,u32r,NodeGen3.keyOf,NodeGen3.isLeaf,List.getD_eq_getElem?_getD,
      List.getElem?_append,hl,Nat.add_comm]
  | ext =>
    simp only [hn,NodeGen3.keyOf,NodeGen3.isLeaf] at hl
    simp [NodeV3.ser,u32r,NodeGen3.keyOf,NodeGen3.isLeaf,List.getD_eq_getElem?_getD,
      List.getElem?_append,hl,Nat.add_comm]
  | branch => simp [hn,NodeGen3.isLE] at hs

theorem MovedPrefix.flag_byte {I : UpsInst} {Q : UpsPartI} {dst : NodeEncoding Q}
    (m : MovedPrefix I Q dst) (f : FieldsOk Q) (hk : Q.kind=6 ∨ Q.kind=7)
    {p : Nat} (hp : p<Q.q.length) (hs : (fieldAt Q.shape p).1=2) :
    Q.q.getD p 0 = 32*NodeGen.b2n (NodeGen3.isLeaf dst.node)+16*Q.qodd+
      Q.qodd*(Q.pb.getD (sposV I Q 2 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p).toNat 0%16) := by
  have hkind : Q.kind=6 ∨ Q.kind=7 ∨ XcpB I Q=true := by
    rcases hk with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
  have hsrc := m.header.prefixNode hkind
  have hd := m.prefixNode
  have hqt : Q.ty≤1 := by
    rw [dst.ty]
    cases hn : dst.node with
    | leaf => simp [nodeTypeCode]
    | ext => simp [nodeTypeCode]
    | branch => simp [hn,NodeGen3.isLE] at hd
  have hp5 := f.hpf_position hqt hs
  have hq : Q.qhk = 1 + (NodeGen3.keyOf dst.node).length/2 := by
    rw [dst.hplen]; simp [NodeGen3.hplenOf,hd]
  have hph : Q.phk = 1 + (NodeGen3.keyOf m.source.node).length/2 := by
    rw [m.header.hplen]; simp [NodeGen3.hplenOf,hsrc]
  have ho : Q.qodd=(NodeGen3.keyOf dst.node).length%2 := by
    rw [dst.odd]; simp [NodeGen3.oddOf,hd]
  have hl : (NodeGen3.keyOf dst.node).length=(NodeGen3.keyOf m.source.node).length-(I.ti+1) := by
    rw [m.key,List.length_drop]
  have hle : Q.qhk≤Q.phk := by omega
  have hpos : (sposV I Q 2 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p).toNat=5+(Q.phk-Q.qhk) := by
    rcases hk with hk | hk <;> simp [sposV,hk,hp5] <;> omega
  rw [hpos,m.header.key_byte hkind (by omega)]
  have he : Q.phk-Q.qhk=(NodeGen3.keyOf m.source.node).length/2-(NodeGen3.keyOf dst.node).length/2 := by omega
  rw [he,dst.prefixByte hp hs,ho,m.key,m.leaf]
  exact hpN_drop_head _ _ _ (NodeGen3.key_nib m.source.wf) (by omega)

end ZkFormal.NearV3.Render.UpsGen
