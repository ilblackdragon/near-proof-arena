import ZkFormal.NearV3.Qv.Candidates.CombinedPlanOrder

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

def rowOffset (ws : List Walk) (i : Nat) : Nat := ((ws.take i).flatMap Walk.rows).length

@[simp] theorem rowOffset_zero (ws : List Walk) : rowOffset ws 0=0 := by simp [rowOffset]

@[simp] theorem rowOffset_cons (w : Walk) (ws : List Walk) (i : Nat) :
    rowOffset (w::ws) (i+1)=w.rows.length+rowOffset ws i := by
  simp [rowOffset,List.flatMap_cons]

theorem flat_rows_at (ws : List Walk) (d : Walk) (i pos : Nat)
    (hi : i<ws.length) (hp : pos<(ws.getD i d).rows.length) :
    (ws.flatMap Walk.rows).getD (rowOffset ws i+pos) []=(ws.getD i d).rows.getD pos [] := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero =>
      have hpos : pos<w.rows.length := by simpa using hp
      simp only [rowOffset_zero,Nat.zero_add,List.getD_cons_zero,List.flatMap_cons]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hpos]
    | succ i =>
      have hii : i<ws.length := by simpa using hi
      have hpp : pos<(ws.getD i d).rows.length := by simpa using hp
      have hle : w.rows.length≤w.rows.length+rowOffset ws i+pos := by omega
      simp only [rowOffset_cons,List.getD_cons_succ,List.flatMap_cons,List.getD_eq_getElem?_getD,
        List.getElem?_append_right hle]
      have he : w.rows.length+rowOffset ws i+pos-w.rows.length=rowOffset ws i+pos := by omega
      rw [he]
      exact ih i hii hpp

theorem flat_rows_location (ws : List Walk) (d : Walk) (r : Nat)
    (hr : r<(ws.flatMap Walk.rows).length) :
    ∃ i pos, i<ws.length ∧ pos<(ws.getD i d).rows.length ∧ r=rowOffset ws i+pos := by
  induction ws generalizing r with
  | nil => simp at hr
  | cons w ws ih =>
    by_cases hw : r<w.rows.length
    · exact ⟨0,r,by simp,by simpa using hw,by simp⟩
    · have ht : r-w.rows.length<(ws.flatMap Walk.rows).length := by
        simp only [List.flatMap_cons,List.length_append] at hr
        omega
      obtain ⟨i,pos,hi,hp,he⟩ := ih (r-w.rows.length) ht
      refine ⟨i+1,pos,by simpa using hi,by simpa using hp,?_⟩
      rw [rowOffset_cons]
      omega

theorem Walk.rows_at (w : Walk) (pos : Nat) (hp : pos<w.kind.bytes.length) :
    w.rows.getD pos []=w.row pos (w.kind.bytes.getD pos 0) := by
  simp [Walk.rows,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_zipIdx,
    List.getElem?_eq_getElem hp]

theorem rowOffset_next (ws : List Walk) (d : Walk) (i : Nat) (hi : i<ws.length) :
    rowOffset ws (i+1)=rowOffset ws i+(ws.getD i d).rows.length := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hii : i<ws.length := by simpa using hi
      simp only [rowOffset_cons,List.getD_cons_succ]
      rw [ih i hii,Nat.add_assoc]

theorem rowOffset_end (ws : List Walk) : rowOffset ws ws.length=(ws.flatMap Walk.rows).length := by
  simp [rowOffset]

theorem flat_rows_boundary (ws : List Walk) (d : Walk) (i pos : Nat)
    (hi : i+1<ws.length) (hp : pos+1=(ws.getD i d).rows.length)
    (hn : 0<(ws.getD (i+1) d).rows.length) :
    (ws.flatMap Walk.rows).getD (rowOffset ws i+pos+1) []=
      (ws.getD (i+1) d).rows.getD 0 [] := by
  have ho := rowOffset_next ws d i (by omega)
  have he : rowOffset ws i+pos+1=rowOffset ws (i+1)+0 := by omega
  rw [he]
  exact flat_rows_at ws d (i+1) 0 hi hn

theorem flat_rows_generated (ws : List Walk) (d : Walk) (r : Nat)
    (hr : r<(ws.flatMap Walk.rows).length) :
    ∃ i pos, i<ws.length ∧ pos<(ws.getD i d).kind.bytes.length ∧
      r=rowOffset ws i+pos ∧
      (ws.flatMap Walk.rows).getD r []=
        (ws.getD i d).row pos ((ws.getD i d).kind.bytes.getD pos 0) := by
  obtain ⟨i,pos,hi,hp,he⟩ := flat_rows_location ws d r hr
  have hb : pos<(ws.getD i d).kind.bytes.length := by simpa [Walk.rows_length] using hp
  refine ⟨i,pos,hi,hb,he,?_⟩
  rw [he,flat_rows_at ws d i pos hi hp,Walk.rows_at _ pos hb]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
