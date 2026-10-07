import ZkFormal.NearV3.Render.Ups.SplitBitmap

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render
open NodeGen (F)

theorem NodeEncoding.bitmap {Q : UpsPartI} (e : NodeEncoding Q) {p : Nat}
    (hp : p < Q.q.length) (hs : (fieldAt Q.shape p).1=6) :
    Q.q.getD p 0 = if (fieldAt Q.shape p).2.1=0 then kidBitmap (NodeGen3.kidsOf e.node)%256
      else kidBitmap (NodeGen3.kidsOf e.node)/256 := by
  obtain ⟨f,hf,hstate,hidx,hbyte⟩ := e.byte_field hp
  have hbm : f = .bm := by
    cases f <;> simp [F.state,Node.sTAG,Node.sHPL,Node.sHPF,Node.sKEY,Node.sVLEN,Node.sVH,
      Node.sBM,Node.sCH,Node.sMEM,hs] at hstate ⊢
  subst f
  have ht := (NodeGen3.kind_facts hf).2.2.1 rfl
  have hb : NodeGen3.bmvOf e.node=kidBitmap (NodeGen3.kidsOf e.node) := by
    cases hn : e.node with
    | leaf => simp [hn,NodeGen3.typeOf] at ht
    | ext => simp [hn,NodeGen3.typeOf] at ht
    | branch => rfl
  simp only [F.len] at hidx
  rw [hbyte]
  simp only [NodeGen3.fbytes,hb]
  rcases (show (fieldAt Q.shape p).2.1=0 ∨ (fieldAt Q.shape p).2.1=1 by omega) with hi | hi <;>
    rw [hi] <;> simp

theorem SplitBitmap.byte {I : UpsInst} {Q : UpsPartI} {e : NodeEncoding Q}
    (h : SplitBitmap I Q e) (hk : Q.kind=10) {p : Nat}
    (hp : p < Q.q.length) (hs : (fieldAt Q.shape p).1=6) :
    (Q.q.getD p 0 : Int) = if (fieldAt Q.shape p).2.1=0 then bmLV I else bmHV I := by
  rw [e.bitmap hp hs]
  by_cases hi : (fieldAt Q.shape p).2.1=0
  · rw [if_pos hi,if_pos hi]; exact h.low hk
  · rw [if_neg hi,if_neg hi]; exact h.high hk

end ZkFormal.NearV3.Render.UpsGen
