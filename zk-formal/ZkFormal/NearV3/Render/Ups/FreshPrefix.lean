import ZkFormal.NearV3.Render.Ups.NodeHeaderBytes

/-! Ordinary key semantics for newly created leaves, wrapping extensions, and
pass-through extensions. These describe nibble lists, not AIR evaluations. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render
open NodeGen (F)

structure FreshPrefix (I : UpsInst) (Q : UpsPartI) (e : NodeEncoding Q) : Prop where
  terminal : 1 ≤ I.ts ∧ I.ts ≤ 3
  leaf : Q.kind = 8 → NodeGen3.keyOf e.node = [0,15].drop I.ts ∧ NodeGen3.isLeaf e.node = true
  wrap : Q.kind = 9 →
    (I.ts=2 ∧ I.ti=1 ∨ I.ts=3 ∧ I.ti=1 ∨ I.ts=3 ∧ I.ti=2) ∧
    NodeGen3.keyOf e.node = ([0,15].drop (I.ts-1-I.ti)).take I.ti ∧ NodeGen3.isLeaf e.node = false
  pass : Q.kind = 11 → NodeGen3.keyOf e.node = [] ∧ NodeGen3.isLeaf e.node = false

theorem NodeEncoding.prefixByte {Q : UpsPartI} (e : NodeEncoding Q) {p : Nat}
    (hp : p < Q.q.length) (hs : (fieldAt Q.shape p).1=2) :
    Q.q.getD p 0 = (hpN (NodeGen3.keyOf e.node) (NodeGen3.isLeaf e.node)).getD 0 0 := by
  obtain ⟨f,hf,hstate,hidx,hbyte⟩ := e.byte_field hp
  have htag : f = .hpf := by
    cases f <;> simp [F.state,Node.sTAG,Node.sHPL,Node.sHPF,Node.sKEY,Node.sVLEN,Node.sVH,
      Node.sBM,Node.sCH,Node.sMEM,hs] at hstate ⊢
  subst f
  have hi : (fieldAt Q.shape p).2.1=0 := by simp only [F.len] at hidx; omega
  rw [hbyte,hi]
  simp [NodeGen3.fbytes,List.getD_eq_getElem?_getD]

theorem FreshPrefix.nlf_byte {I : UpsInst} {Q : UpsPartI} {e : NodeEncoding Q}
    (h : FreshPrefix I Q e) {p : Nat} (hp : p < Q.q.length)
    (hs : (fieldAt Q.shape p).1=2) (hk : Q.kind=8) :
    Q.q.getD p 0 = if I.ts=1 then 63 else 32 := by
  rw [e.prefixByte hp hs,(h.leaf hk).1,(h.leaf hk).2]
  have ht := h.terminal
  rcases (show I.ts=1 ∨ I.ts=2 ∨ I.ts=3 by omega) with ht | ht | ht <;> rw [ht] <;> decide

theorem FreshPrefix.pass_byte {I : UpsInst} {Q : UpsPartI} {e : NodeEncoding Q}
    (h : FreshPrefix I Q e) {p : Nat} (hp : p < Q.q.length)
    (hs : (fieldAt Q.shape p).1=2) (hk : Q.kind=11) : Q.q.getD p 0=0 := by
  rw [e.prefixByte hp hs,(h.pass hk).1,(h.pass hk).2]; rfl

theorem FreshPrefix.wrap_byte {I : UpsInst} {Q : UpsPartI} {e : NodeEncoding Q}
    (h : FreshPrefix I Q e) {p : Nat} (hp : p < Q.q.length)
    (hs : (fieldAt Q.shape p).1=2) (hk : Q.kind=9) :
    Q.q.getD p 0 = if I.ti=1 then (if I.ts=2 then 16 else 31) else 0 := by
  rw [e.prefixByte hp hs,(h.wrap hk).2.1,(h.wrap hk).2.2]
  rcases (h.wrap hk).1 with ⟨ht,hi⟩ | ⟨ht,hi⟩ | ⟨ht,hi⟩ <;> rw [ht,hi] <;> decide

theorem FreshPrefix.wrap_key {I : UpsInst} {Q : UpsPartI} {e : NodeEncoding Q}
    (h : FreshPrefix I Q e) {p : Nat} (hp : p < Q.q.length)
    (hs : (fieldAt Q.shape p).1=3) (hk : Q.kind=9) : Q.q.getD p 0=15 := by
  obtain ⟨f,hf,hstate,hidx,hbyte⟩ := e.byte_field hp
  have hkey : f = .key := by
    cases f <;> simp [F.state,Node.sTAG,Node.sHPL,Node.sHPF,Node.sKEY,Node.sVLEN,Node.sVH,
      Node.sBM,Node.sCH,Node.sMEM,hs] at hstate ⊢
  subst f
  have hl : NodeGen3.hplenOf e.node = 1 + (NodeGen3.keyOf e.node).length / 2 := by
    have hh := (NodeGen3.kind_facts hf).1 (Or.inr (Or.inr rfl))
    cases hn : e.node with
    | leaf => rfl
    | ext => rfl
    | branch sv kids m => cases sv <;> simp [hn,NodeGen3.typeOf] at hh
  simp only [F.len,hl,(h.wrap hk).2.1] at hidx
  rw [hbyte]
  simp only [NodeGen3.fbytes,(h.wrap hk).2.1,(h.wrap hk).2.2]
  rcases (h.wrap hk).1 with ⟨ht,hi⟩ | ⟨ht,hi⟩ | ⟨ht,hi⟩ <;> rw [ht,hi] at hidx ⊢
  · simp at hidx
  · simp at hidx
  · have hx : (fieldAt Q.shape p).2.1=0 := by simpa using hidx
    rw [hx]; rfl

end ZkFormal.NearV3.Render.UpsGen
