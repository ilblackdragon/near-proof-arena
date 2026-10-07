import ZkFormal.NearV3.Render.Ups.WideCarryBounds
import ZkFormal.NearV3.Render.Ups.MemInput
import ZkFormal.NearV3.Render.Ups.MemModulo
import ZkFormal.NearV3.Render.Ups.NodeHeaderBytes
import ZkFormal.NearV3.Render.UniqGen

/-! Construct memory-row obligations from an ordinary serialized node, its
scalar memory usage, and bounds on the arithmetic operands. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render
open NodeGen (F)

theorem NodeEncoding.memory_byte {Q : UpsPartI} (e : NodeEncoding Q)
    {p : Nat} (hp : p < Q.q.length) (hs : (fieldAt Q.shape p).1 = 8) :
    Q.q.getD p 0 = (NodeGen3.memOf e.node).getD (fieldAt Q.shape p).2.1 0 := by
  obtain ⟨f,hf,hstate,hidx,hbyte⟩ := e.byte_field hp
  have hm : f = .mem := by
    cases f <;> simp [F.state,Node.sTAG,Node.sHPL,Node.sHPF,Node.sKEY,Node.sVLEN,Node.sVH,
      Node.sBM,Node.sCH,Node.sMEM,hs] at hstate ⊢
  subst f
  exact hbyte

/-- The serialized memory field has exactly eight digit positions. -/
theorem NodeEncoding.memory_index {Q : UpsPartI} (e : NodeEncoding Q)
    {p : Nat} (hp : p<Q.q.length) (hs : (fieldAt Q.shape p).1=8) :
    (fieldAt Q.shape p).2.1<8 := by
  obtain ⟨f,hf,hstate,hidx,hbyte⟩ := e.byte_field hp
  have hm : f=.mem := by
    cases f <;> simp [F.state,Node.sTAG,Node.sHPL,Node.sHPF,Node.sKEY,Node.sVLEN,Node.sVH,
      Node.sBM,Node.sCH,Node.sMEM,hs] at hstate ⊢
  subst f
  exact hidx

/-- A modular equality to the node's decoded memory usage implies every
serialized MEM byte equation; these are no longer assumed individually. -/
theorem NodeEncoding.memory_result {I : UpsInst} {Q : UpsPartI} (e : NodeEncoding Q)
    (hb : ∀ b ∈ NodeGen3.memOf e.node, b < 256)
    (hr : RV I Q % 256^8 = (le256 (NodeGen3.memOf e.node) : Int))
    {p : Nat} (hp : p < Q.q.length) (hs : (fieldAt Q.shape p).1 = 8) :
    (Q.q.getD p 0 : Int) = RV I Q / 256 ^ (fieldAt Q.shape p).2.1 % 256 := by
  rw [e.memory_byte hp hs,low64_digit (RV I Q) (e.memory_index hp hs),hr]
  have h := UniqGen.byte_le256 (NodeGen3.memOf e.node) (fieldAt Q.shape p).2.1 hb
  exact congrArg (fun x : Nat => (x : Int)) h.symm

/-- Semantic arithmetic sufficient for memory completeness. These are bounds
on operands and modular equality of an ordinary decoded node value, not AIR equations. -/
theorem memOk_of_semantics {I : UpsInst} {Q : UpsPartI} (e : NodeEncoding Q)
    (hb : ∀ b ∈ NodeGen3.memOf e.node, b < 256)
    (hr : RV I Q % 256^8 = (le256 (NodeGen3.memOf e.node) : Int))
    (hn : Q.neg ≤ 1)
    (hx : ∀ i, i < 7 → -(2^23+1024) ≤ sigV Q * X1V I Q i ∧ sigV Q * X1V I Q i ≤ 2^23+1024)
    (he : ∀ i, i < 8 → 0 ≤ EinV I Q i ∧ EinV I Q i ≤ 2^23+1024)
    (ht : 0 ≤ TV I Q ∧ TV I Q < 131072 * 256 ^ 8) : MemOk I Q where
  carries i hi := ⟨(encoded_inside_widebounds I Q hx ht i hi).1,(encoded_inside_widebounds I Q hx ht i hi).2,
    (co2V_widebounds I Q hn he i hi).1,(co2V_widebounds I Q hn he i hi).2⟩
  bytes p hp hs := e.memory_result hb hr hp hs

end ZkFormal.NearV3.Render.UpsGen
