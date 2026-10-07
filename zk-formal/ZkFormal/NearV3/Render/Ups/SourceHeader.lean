import ZkFormal.NearV3.Render.Ups.SourceLayout
import ZkFormal.NearV3.Render.Ups.ReadBits
import ZkFormal.NearV3.Render.Node.ByteFacts

/-! Source header metadata refers to an actual serialized source node. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

structure SourceHeader (I : UpsInst) (Q : UpsPartI) (e : SourceLayout Q) : Prop where
  hplen : Q.phk = NodeGen3.hplenOf e.node
  odd : Q.podd = NodeGen3.oddOf e.node
  prefixNode : Q.kind=6 ∨ Q.kind=7 ∨ XcpB I Q=true → NodeGen3.isLE e.node=true
  leaf : Q.kind=6 ∨ Q.kind=7 ∨ XcpB I Q=true →
    (Q.ty=0 ↔ NodeGen3.isLeaf e.node=true)
  insertValue : Q.kind=4 → nodeTypeCode e.node=2

theorem SourceHeader.hpl {I : UpsInst} {Q : UpsPartI} {e : SourceLayout Q}
    (h : SourceHeader I Q e) (hk : Q.kind=6 ∨ Q.kind=7 ∨ XcpB I Q=true)
    (i : Nat) (hi : i < 4) : Q.pb.getD (1+i) 0 = (u32Bytes Q.phk).getD i 0 := by
  have hs := h.prefixNode hk
  rw [e.bytes,h.hplen]
  cases hn : e.node with
  | leaf => simp [NodeV3.ser,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,
      NodeGen3.hpN_len,List.getD_eq_getElem?_getD,List.getElem?_append,hi,Nat.add_comm]
  | ext => simp [NodeV3.ser,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,
      NodeGen3.hpN_len,List.getD_eq_getElem?_getD,List.getElem?_append,hi,Nat.add_comm]
  | branch => simp [hn,NodeGen3.isLE] at hs

/-- The complete authenticated source length binds its HP length without truncation. -/
theorem SourceHeader.length {I : UpsInst} {Q : UpsPartI} {e : SourceLayout Q}
    (h : SourceHeader I Q e) (hk : Q.kind=6 ∨ Q.kind=7 ∨ XcpB I Q=true) :
    (Q.pb.length : Int) = 45 + 4 * ind (Q.ty=0) + Q.phk := by
  have hs := h.prefixNode hk
  have hl := h.leaf hk
  have hw := e.wf
  rw [e.bytes,h.hplen]
  cases hn : e.node with
  | branch => simp [hn,NodeGen3.isLE] at hs
  | leaf k v m =>
    have ht : Q.ty=0 := hl.mpr (by simp [hn,NodeGen3.isLeaf])
    simp only [hn,NodeV3.wf] at hw
    rcases hw with ⟨_,hv,hm⟩
    cases v <;> simp_all [NodeV3.ser,NSlot3.bytes,NSlot3.wf,NodeGen3.hplenOf,
      NodeGen3.keyOf,NodeGen3.isLE,NodeGen3.hpN_len,ind] <;> omega
  | ext k v m =>
    have ht : Q.ty≠0 := by intro ht; have := hl.mp ht; simp [hn,NodeGen3.isLeaf] at this
    simp only [hn,NodeV3.wf] at hw
    rcases hw with ⟨_,hne,hv,hm⟩
    cases v <;> simp_all [NodeV3.ser,NKid.bytes,NKid.wf,NodeGen3.hplenOf,
      NodeGen3.keyOf,NodeGen3.isLE,NodeGen3.hpN_len,ind] <;> omega

theorem SourceHeader.flag {I : UpsInst} {Q : UpsPartI} {e : SourceLayout Q}
    (h : SourceHeader I Q e) (hk : Q.kind=6 ∨ Q.kind=7 ∨ XcpB I Q=true) :
    Q.pb.getD 5 0 = (hpN (NodeGen3.keyOf e.node) (NodeGen3.isLeaf e.node)).getD 0 0 := by
  have hs := h.prefixNode hk
  rw [e.bytes]
  cases hn : e.node with
  | leaf => simp [NodeV3.ser,u32Bytes_length,NodeGen3.keyOf,NodeGen3.isLeaf,List.getD_eq_getElem?_getD,
      List.getElem?_append,NodeGen3.hpN_len] <;> split <;> (first | rfl | omega)
  | ext => simp [NodeV3.ser,u32Bytes_length,NodeGen3.keyOf,NodeGen3.isLeaf,List.getD_eq_getElem?_getD,
      List.getElem?_append,NodeGen3.hpN_len] <;> split <;> (first | rfl | omega)
  | branch => simp [hn,NodeGen3.isLE] at hs

theorem SourceHeader.flag_high {I : UpsInst} {Q : UpsPartI} {e : SourceLayout Q}
    (h : SourceHeader I Q e) (hk : Q.kind=6 ∨ Q.kind=7 ∨ XcpB I Q=true) :
    (Q.pb.getD 5 0 : Int)/16 = 2*ind (Q.ty=0)+(Q.podd : Int) := by
  rw [h.flag hk]
  have hnib := NodeGen3.key_nib e.wf
  have hh := NodeLay.hp_head (NodeGen3.keyOf e.node) (NodeGen3.isLeaf e.node) hnib
  have hb : (NodeGen3.keyOf e.node).getD 0 0 < 16 := by
    rw [List.getD_eq_getElem?_getD]
    cases he : (NodeGen3.keyOf e.node)[0]? with
    | none => simp
    | some b => exact hnib b (List.mem_of_getElem? he)
  simp only [List.getD_eq_getElem?_getD] at hb
  have hs := h.prefixNode hk
  have ho : Q.podd=(NodeGen3.keyOf e.node).length%2 := by rw [h.odd]; simp [NodeGen3.oddOf,hs]
  have hl := h.leaf hk
  rw [hh,ho]
  by_cases ht : Q.ty=0
  · have ht' := hl.mp ht
    simp [NodeGen.b2n,ht',ind,ht]; split <;> omega
  · have ht' : NodeGen3.isLeaf e.node=false := by cases hh : NodeGen3.isLeaf e.node <;> simp_all
    simp [NodeGen.b2n,ht',ind,ht]; split <;> omega

theorem SourceHeader.insert_tag {I : UpsInst} {Q : UpsPartI} {e : SourceLayout Q}
    (h : SourceHeader I Q e) (hk : Q.kind=4) : Q.pb.getD 0 0=1 := by
  have ht := h.insertValue hk
  rw [e.bytes]
  cases hn : e.node with
  | leaf => simp [hn,nodeTypeCode] at ht
  | ext => simp [hn,nodeTypeCode] at ht
  | branch sv kids mem => cases sv with
    | none => rfl
    | some => simp [hn,nodeTypeCode] at ht

end ZkFormal.NearV3.Render.UpsGen
