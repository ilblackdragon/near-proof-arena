import ZkFormal.NearV3.Render.Ups.CopyAddress
import ZkFormal.NearV3.Render.Ups.CopyPayload

namespace ZkFormal.NearV3.Render.UpsGen

theorem CopyFields.byte {I : UpsInst} {Q : UpsPartI} (copy : CopyFields I Q)
    (f : FieldsOk Q) (hkind : Q.kind<12) {p : Nat} (hp : p<Q.q.length)
    (hc : CpB I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2=true) :
    (Q.q.getD p 0 : Int)=rbV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p+
      bitmapDelta (Q.kind==5 && (fieldAt Q.shape p).1==6) I.ts (fieldAt Q.shape p).2.1 := by
  obtain ⟨pre,post,hshape,hpos,hwin,hwidth⟩ := fieldAt_decompose Q.shape p (by rw [← f.bytes]; exact hp)
  obtain ⟨hk8,hstart,hpayload⟩ := copy.fields pre post _ _ hshape (by rw [← hwin]; exact hc)
  have hix : (Q.kind==5 && (fieldAt Q.shape p).1==6)=true → (fieldAt Q.shape p).2.1<2 := by
    intro hpatch
    have hs : (fieldAt Q.shape p).1=6 := by simp only [Bool.and_eq_true,beq_iff_eq] at hpatch; exact hpatch.2
    have hm := (fieldAt_bounds Q.shape p (by rw [← f.bytes]; exact hp)).2
    have hm' : ((fieldAt Q.shape p).1,(fieldAt Q.shape p).2.2.1) ∈ nodeFields Q.ty Q.qhk (nWin Q.shape) := by rw [← f.shape]; exact hm
    have hl := (nodeFields_length hm').2.2.2.2.2.2.1 hs
    omega
  have hb := hpayload.byte (ts:=I.ts) (ix:=(fieldAt Q.shape p).2.1) rfl hix
  rw [field_slice_get _ _ _ _ hwidth,field_slice_get _ _ _ _ hwidth,← hpos] at hb
  have ha := copy_address (I:=I) hkind (f.state hp) hk8 hc hpos
  rw [hwin] at ha
  have haddr : (sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p).toNat=
      (sourceFieldStart I Q (fieldAt Q.shape p).1 (nWin pre) (fieldsLen pre)).toNat+(fieldAt Q.shape p).2.1 := by
    rw [hwin,ha]
    omega
  simpa only [rbV,haddr] using hb

theorem bitmapDelta_flags (I : UpsInst) (Q : UpsPartI) (st ix : Nat) :
    bitmapDelta (Q.kind==5 && st==6) I.ts ix =
      ind (st=6) * (ind (ix=0)*ba0V I Q + (1 + -ind (ix=0))*ba1V I Q) := by
  by_cases hk : Q.kind=5 <;> by_cases hs : st=6 <;> by_cases hi : ix=0 <;> by_cases ht : I.ts=1 <;>
    simp [bitmapDelta,ba0V,ba1V,ind,hk,hs,hi,ht]

end ZkFormal.NearV3.Render.UpsGen
