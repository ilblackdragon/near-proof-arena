import ZkFormal.NearV3.Render.Ups.MemPosition

namespace ZkFormal.NearV3.Render.UpsGen

theorem FieldsOk.footer_length {Q : UpsPartI} (ok : FieldsOk Q) :
    Q.q.length=fieldsLen (nodeHeader Q.ty Q.qhk)+32*nWin Q.shape+8 := by
  calc
    Q.q.length=fieldsLen (nodeFields Q.ty Q.qhk (nWin Q.shape)) := ok.bytes.trans (congrArg fieldsLen ok.shape)
    _ = _ := by rw [nodeFields_eq_header,fieldsLen_append,fieldsLen_windows]; omega

/-- Every serialized node has a nonempty final memory field. -/
theorem FieldsOk.positive {Q : UpsPartI} (ok : FieldsOk Q) : 1≤Q.q.length := by
  have h := ok.footer_length
  omega

/-- The last serialized byte is exactly the last byte of MEM, in both directions. -/
theorem FieldsOk.memEnd {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat} (hp : p<Q.q.length) :
    p+1=Q.q.length ↔ (fieldAt Q.shape p).1=8 ∧
      (fieldAt Q.shape p).2.1+1=(fieldAt Q.shape p).2.2.1 := by
  constructor
  · intro he
    have hl := ok.footer_length
    have hshape : Q.shape=nodeHeader Q.ty Q.qhk++
        (List.replicate (nWin Q.shape) (7,32)++[(8,8)]) := by
      rw [←nodeFields_eq_header]; exact ok.shape
    have hc := fieldAt_append_after (nodeHeader Q.ty Q.qhk)
      (List.replicate (nWin Q.shape) (7,32)++[(8,8)]) p (by omega)
    rw [←hshape,fieldAt_after_windows _ _ (by omega) (by omega)] at hc
    rw [hc]
    constructor
    · rfl
    · change p-fieldsLen (nodeHeader Q.ty Q.qhk)-32*nWin Q.shape+1=8
      omega
  · rintro ⟨hs,hi⟩
    have hpos := ok.mem_position hp hs
    have hf := (fieldAt_bounds Q.shape p (by rw [←ok.bytes]; exact hp)).2
    have hf' : ((fieldAt Q.shape p).1,(fieldAt Q.shape p).2.2.1)∈nodeFields Q.ty Q.qhk (nWin Q.shape) := by
      rw [←ok.shape]; exact hf
    have hlen := (nodeFields_length hf').2.2.2.2.2.2.2.2 hs
    omega
end ZkFormal.NearV3.Render.UpsGen
