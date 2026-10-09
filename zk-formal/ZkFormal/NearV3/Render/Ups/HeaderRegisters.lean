import ZkFormal.NearV3.Render.Ups.NodeHeaderBytes
import ZkFormal.NearV3.Render.Ups.ByteWindows

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near

/-- HPL uses accumulator registers only; digest, nibble and MEM registers are on other fields. -/
theorem header_regs (I : UpsInst) (Q : UpsPartI) (k p ix fl wi u : Nat) :
    QC I Q k p 1 ix fl wi u 137 = (le256 ((u32Bytes Q.qhk).take (ix+1)) : Int) ∧
    QC I Q k p 1 ix fl wi u 138 = (256^ix : Nat) := by
  simp [QC,isSeg,isPC,qRow,winFrV,WinFrB,ind]

theorem FieldsOk.header_width {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat}
    (hp : p<Q.q.length) (hs : (fieldAt Q.shape p).1=1) :
    (fieldAt Q.shape p).2.2.1=4 := by
  have hm := (fieldAt_bounds Q.shape p (by rw [← ok.bytes]; exact hp)).2
  have hn : ((fieldAt Q.shape p).1,(fieldAt Q.shape p).2.2.1) ∈ nodeFields Q.ty Q.qhk (nWin Q.shape) := by
    rw [← ok.shape]; exact hm
  exact (nodeFields_length hn).2.1 hs

end ZkFormal.NearV3.Render.UpsGen
