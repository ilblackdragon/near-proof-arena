import ZkFormal.NearV3.Render.Ups.WindowCursor
import ZkFormal.NearV3.Render.Ups.FieldDecompose

namespace ZkFormal.NearV3.Render.UpsGen

theorem field_start_cursor (pre post : List (Nat×Nat)) (st width : Nat) (hw : 0<width) :
    fieldAt (pre++(st,width)::post) (fieldsLen pre)=(st,0,width,nWin pre) := by
  rw [fieldAt_append_after _ _ _ (by omega)]
  simp [fieldAt,hw]

theorem field_start_window {Q : UpsPartI} (f : FieldsOk Q) (pre post : List (Nat×Nat))
    (width : Nat) (hs : Q.shape=pre++(7,width)::post) :
    width=32 ∧ fieldsLen pre=fieldsLen (nodeHeader Q.ty Q.qhk)+32*nWin pre ∧ nWin pre<nWin Q.shape := by
  have hm : (7,width)∈nodeFields Q.ty Q.qhk (nWin Q.shape) := by rw [←f.shape,hs]; simp
  have hw := (nodeFields_length hm).2.2.2.2.2.2.2.1 rfl
  have hc : fieldAt Q.shape (fieldsLen pre)=(7,0,width,nWin pre) := by
    rw [hs]; exact field_start_cursor pre post 7 width (by omega)
  have hh := f.window (show (fieldAt Q.shape (fieldsLen pre)).1=7 by rw [hc])
  rw [hc] at hh
  have hi := congrArg (fun t : Nat×Nat×Nat×Nat => t.2.1) hh.2.2
  have hn := congrArg (fun t : Nat×Nat×Nat×Nat => t.2.2.2) hh.2.2
  dsimp at hi hn
  omega

end ZkFormal.NearV3.Render.UpsGen
