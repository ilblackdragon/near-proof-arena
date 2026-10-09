import ZkFormal.NearV3.Render.Ups.SourceLayout
import ZkFormal.NearV3.Render.Node.HeaderBounds

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near Render Render.UpsGen

/-- Every actual node serialization contains a tag and its eight-byte memory
field in addition to any hex-prefix payload. -/
theorem node_source_room (v : NodeV3) (hw : v.wf) (post : Bool) :
    NodeGen3.hplenOf v+9≤(v.ser post).length := by
  cases v with
  | leaf key v mem =>
    have hm:=hw.2.2
    simp [NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,NodeV3.ser,NodeGen3.hpN_len,hm] <;> omega
  | ext key kid mem =>
    have hm:=hw.2.2.2
    simp [NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,NodeV3.ser,NodeGen3.hpN_len,hm] <;> omega
  | branch v kids mem =>
    have hm:=hw.2.2.2
    cases v <;> simp [NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,NodeV3.ser,hm] <;> omega

theorem source_layout_room {Q : UpsPartI} (e : SourceLayout Q) : 9≤Q.pb.length := by
  have h:=node_source_room e.node e.wf true
  rw [e.bytes]
  omega

/-- Memory reads use the final eight physical source bytes. -/
theorem memory_read_bounds {I : UpsInst} {Q : UpsPartI} (f : FieldsOk Q)
    (e : SourceLayout Q) {p : Nat} (hp : p<Q.q.length)
    (hs : (fieldAt Q.shape p).1=8) :
    0≤sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p ∧
    (sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p).toNat<Q.pb.length := by
  have hm:=f.mem_position hp hs
  have hb:=source_layout_room e
  simp only [sposV,hs,ite_true]
  constructor <;> omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
