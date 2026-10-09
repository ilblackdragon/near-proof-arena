import ZkFormal.NearV3.Render.Ups.CopyAddress

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open Render Render.UpsGen

private theorem edit_length {b : Bool} {x : Nat} {a c : List Nat}
    (h : FieldPayloadEdit b x a c) : a.length=c.length := by
  cases h <;> rfl

/-- Whole serialized-field copying authenticates an in-range source byte, including
its signed renderer address, rather than merely an out-of-range getD default. -/
theorem copy_read_bounds {I : UpsInst} {Q : UpsPartI} (copy : CopyFields I Q)
    (f : FieldsOk Q) (hkind : Q.kind<12) {p : Nat} (hp : p<Q.q.length)
    (hc : CpB I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2=true) :
    Q.kind≠8 ∧
    0≤sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p ∧
    (sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p).toNat<Q.pb.length := by
  obtain ⟨pre,post,hshape,hpos,hwin,hwidth⟩:=
    fieldAt_decompose Q.shape p (by rw [←f.bytes]; exact hp)
  obtain ⟨hk8,hstart,hpayload⟩:=copy.fields pre post _ _ hshape (by rw [←hwin]; exact hc)
  have ha:=copy_address (I:=I) hkind (f.state hp) hk8 hc hpos
  rw [hwin] at ha
  have hout : fieldsLen pre+(fieldAt Q.shape p).2.2.1≤Q.q.length := by
    have hh:=congrArg fieldsLen hshape
    simp only [fieldsLen_append,fieldsLen_cons] at hh
    have hb:=f.bytes
    omega
  have heq : ((Q.pb.drop (sourceFieldStart I Q (fieldAt Q.shape p).1 (nWin pre) (fieldsLen pre)).toNat).take
      (fieldAt Q.shape p).2.2.1).length=
      ((Q.q.drop (fieldsLen pre)).take (fieldAt Q.shape p).2.2.1).length := by
    exact edit_length hpayload
  simp only [List.length_take,List.length_drop] at heq
  refine ⟨hk8,?_,?_⟩
  · rw [hwin,ha]; omega
  · rw [hwin,ha]
    omega

/-- Extra header/value/memory/child reads never belong to a fresh leaf. -/
theorem extra_read_not_fresh {I : UpsInst} {Q : UpsPartI} {st ix wi : Nat}
    (h : ExtraB I Q st ix wi=true) : Q.kind≠8 := by
  intro hk
  simp [ExtraB,RdcB,XcpB,hk] at h

/-- The actual read gate, combined with the honest field-copy contract, excludes
NLF before invoking native source-provider lookup. -/
theorem read_not_fresh {I : UpsInst} {Q : UpsPartI} (copy : CopyFields I Q)
    (f : FieldsOk Q) (hkind : Q.kind<12) {p : Nat} (hp : p<Q.q.length)
    (hr : rdV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.2=1) : Q.kind≠8 := by
  have hb : (CpB I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2 ||
      ExtraB I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2)=true := by
    unfold rdV ind at hr
    split at hr <;> simp_all
  simp only [Bool.or_eq_true] at hb
  rcases hb with hc | he
  · exact (copy_read_bounds copy f hkind hp hc).1
  · exact extra_read_not_fresh he

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
