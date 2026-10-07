import ZkFormal.NearV3.Render.Ups.MoveSuffix
import ZkFormal.NearV3.Render.Ups.CopyMiddle

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

/-- Common copied suffix criterion, discharged by actual node serialization below. -/
theorem moved_copy_suffix (I : UpsInst) (Q : UpsPartI) (hk : Q.kind=6 ∨ Q.kind=7)
    (f : FieldsOk Q) (mid : List (Nat×Nat)) (common oldMem newMem : List Nat)
    (hs : Q.shape=([(0,1),(1,4),(2,1)]++mid)++[(8,8)])
    (hmem : newMem.length=8) (hle : Q.qhk≤Q.phk)
    (hq : Q.q.drop 6=common++newMem)
    (hp : Q.pb.drop (6+(Q.phk-Q.qhk))=common++oldMem) : CopyFields I Q := by
  let front : List (Nat×Nat) := [(0,1),(1,4),(2,1)]
  have hf : fieldsLen front=6 := by simp [front,fieldsLen]
  have hlen : fieldsLen (front++mid)=6+common.length := by
    have hb := f.bytes
    rw [hs,fieldsLen_append] at hb
    have hh := congrArg List.length hq
    simp only [List.length_drop,List.length_append,hmem] at hh
    have he : fieldsLen ([(0,1),(1,4),(2,1)]++mid)=fieldsLen front+fieldsLen mid := fieldsLen_append _ _
    rw [he,hf] at hb
    have he2 : fieldsLen [(8,8)]=8 := rfl
    rw [he2] at hb
    rw [fieldsLen_append,hf]
    omega
  constructor
  intro pre post st width he hc
  have hnot : (st,width) ∉ front ∧ (st,width) ∉ [(8,8)] := by
    have hst : st≠0 ∧ st≠1 ∧ st≠2 ∧ st≠8 := by
      rcases hk with hk|hk <;> simp [CpB,VcpB,hk] at hc <;> omega
    simp [front,hst.1,hst.2.1,hst.2.2.1,hst.2.2.2]
  have hl := field_tail_bound front (mid++[(8,8)]) pre post (st,width)
    (by rw [←he,hs]; simp [front,List.append_assoc]) hnot.1
  have hu := field_headBytes_bound (front++mid) [(8,8)] pre post (st,width)
    (by rw [←he,hs]) hnot.2
  rw [hf] at hl
  rw [hlen] at hu
  have hstart : (sourceFieldStart I Q st (nWin pre) (fieldsLen pre)).toNat=
      fieldsLen pre+(Q.phk-Q.qhk) := by
    rcases hk with hk|hk <;> simp [sourceFieldStart,hk] <;> omega
  have hnonneg : 0≤sourceFieldStart I Q st (nWin pre) (fieldsLen pre) := by
    rcases hk with hk|hk <;> simp [sourceFieldStart,hk] <;> omega
  refine ⟨by omega,hnonneg,?_⟩
  have hb : (Q.q.drop (fieldsLen pre)).take width=
      (Q.pb.drop (fieldsLen pre+(Q.phk-Q.qhk))).take width := by
    have hpidx : 6+(Q.phk-Q.qhk)+(fieldsLen pre-6)=fieldsLen pre+(Q.phk-Q.qhk) := by omega
    have hqidx : 6+(fieldsLen pre-6)=fieldsLen pre := by omega
    rw [←hpidx,←hqidx,←List.drop_drop,←List.drop_drop,hq,hp]
    simpa only [Nat.add_sub_cancel_left] using slice_common_headBytes common newMem oldMem (fieldsLen pre-6) width (by omega)
  have hb5 : (Q.kind==5)=false := by rcases hk with hk|hk <;> simp [hk]
  simp only [hb5,Bool.false_and,hstart]
  rw [←hb]
  exact FieldPayloadEdit.preserve _ _

end ZkFormal.NearV3.Render.UpsGen
