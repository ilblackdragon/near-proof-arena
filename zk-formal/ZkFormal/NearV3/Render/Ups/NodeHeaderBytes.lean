import ZkFormal.NearV3.Render.Ups.NodeEncoding
import ZkFormal.NearV3.Render.Node.FieldFacts

/-! Header bytes derived from ordinary node serialization, not AIR assumptions. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render
open NodeGen (F)

/-- The output byte is the corresponding byte of an actual serializer field. -/
theorem NodeEncoding.byte_field {Q : UpsPartI} (e : NodeEncoding Q) {p : Nat} (hp : p < Q.q.length) :
    ∃ f ∈ NodeGen3.fieldsOf e.node,
      (fieldAt Q.shape p).1 = f.state-14 ∧
      (fieldAt Q.shape p).2.1 < f.len (NodeGen3.hplenOf e.node) ∧
      Q.q.getD p 0 = (NodeGen3.fbytes e.node false f).getD (fieldAt Q.shape p).2.1 0 := by
  have hl : p < (NodeGen.layout (NodeGen3.fieldsOf e.node) (NodeGen3.hplenOf e.node)).length := by
    rw [← NodeGen3.ser_len e.wf false,← e.bytes]; exact hp
  have hm : (NodeGen.layout (NodeGen3.fieldsOf e.node) (NodeGen3.hplenOf e.node)).getD p default ∈
      NodeGen.layout (NodeGen3.fieldsOf e.node) (NodeGen3.hplenOf e.node) := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hl]; exact List.getElem_mem hl
  simp only [NodeGen.layout,List.mem_flatMap,List.mem_map,List.mem_range] at hm
  obtain ⟨f,hf,i,hi,he⟩ := hm
  change (f,i) = (NodeGen.layout (NodeGen3.fieldsOf e.node) (NodeGen3.hplenOf e.node)).getD p default at he
  have hc := e.cursor hp
  rw [← he] at hc
  obtain ⟨hs,hidx⟩ := Prod.mk.inj hc
  refine ⟨f,hf,hs,by omega,?_⟩
  rw [e.bytes,NodeGen3.ser_getD e.wf false hl,← he,hidx]

def tagByte (ty : Nat) : Nat := if ty=0 then 0 else if ty=1 then 3 else if ty=2 then 1 else 2

theorem NodeEncoding.tag {Q : UpsPartI} (e : NodeEncoding Q) {p : Nat} (hp : p < Q.q.length)
    (hs : (fieldAt Q.shape p).1 = 0) : Q.q.getD p 0 = tagByte Q.ty := by
  obtain ⟨f,hf,hstate,hidx,hbyte⟩ := e.byte_field hp
  have htag : f = .tag := by
    cases f <;> simp [F.state,Node.sTAG,Node.sHPL,Node.sHPF,Node.sKEY,Node.sVLEN,Node.sVH,
      Node.sBM,Node.sCH,Node.sMEM,hs] at hstate ⊢
  subst f
  have hi : (fieldAt Q.shape p).2.1 = 0 := by simp only [F.len] at hidx; omega
  rw [hbyte,hi,e.ty]
  cases hn : e.node with
  | leaf => rfl
  | ext => rfl
  | branch sv kids m => cases sv <;> rfl

theorem NodeEncoding.hpl {Q : UpsPartI} (e : NodeEncoding Q) {p : Nat} (hp : p < Q.q.length)
    (hs : (fieldAt Q.shape p).1 = 1) :
    Q.q.getD p 0 = if (fieldAt Q.shape p).2.1 = 0 then Q.qhk else 0 := by
  obtain ⟨f,hf,hstate,hidx,hbyte⟩ := e.byte_field hp
  have htag : f = .hpl := by
    cases f <;> simp [F.state,Node.sTAG,Node.sHPL,Node.sHPF,Node.sKEY,Node.sVLEN,Node.sVH,
      Node.sBM,Node.sCH,Node.sMEM,hs] at hstate ⊢
  subst f
  have hk := (NodeGen3.kind_facts hf).1 (Or.inl rfl)
  simp only [F.len] at hidx
  rw [hbyte,e.hplen]
  by_cases hi : (fieldAt Q.shape p).2.1 = 0
  · rw [if_pos hi,hi]
    cases hn : e.node with
    | leaf => simp [NodeGen3.fbytes,NodeGen3.hpN_len,NodeGen3.hplenOf,NodeGen3.isLE,
        NodeGen3.keyOf,NodeGen3.isLeaf,u32r]
    | ext => simp [NodeGen3.fbytes,NodeGen3.hpN_len,NodeGen3.hplenOf,NodeGen3.isLE,
        NodeGen3.keyOf,NodeGen3.isLeaf,u32r]
    | branch sv kids m => cases sv <;> simp [hn,NodeGen3.typeOf] at hk
  · rw [if_neg hi]
    rcases (show (fieldAt Q.shape p).2.1 = 1 ∨ (fieldAt Q.shape p).2.1 = 2 ∨ (fieldAt Q.shape p).2.1 = 3 by omega)
      with h | h | h <;> rw [h] <;> rfl

end ZkFormal.NearV3.Render.UpsGen
