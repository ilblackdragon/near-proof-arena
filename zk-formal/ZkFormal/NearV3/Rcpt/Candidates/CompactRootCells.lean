import ZkFormal.NearV3.Rcpt.Candidates.CompactRootRows

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows

theorem compact_root_register (Is : List UpsInst) (q i j : Nat) (hj : j<32) :
    compactGeneratedRow Is q (i,.w 3) (UpsV3.reg j)=(inst Is i).post.getD j 0%Algebra.P := by
  have hs : isSeg (UpsV3.reg j)=false := by
    simp [isSeg,UpsV3.reg,show ¬129+j<49 by omega,show ¬176≤129+j by omega,show 129+j≠186 by omega]
  unfold compactGeneratedRow compactRowCell
  simp only [hs,Bool.false_eq_true,ite_false]
  have he : wCell (inst Is i) 3 (UpsV3.reg j)=((inst Is i).post.getD j 0 : Int) := by
    unfold wCell
    split <;> (try (unfold UpsV3.reg at *;omega))
    rw [if_pos (by unfold UpsV3.reg;omega)]
    simp [wReg,UpsV3.reg]
  rw [he]
  exact Fp.toNat_ofNat _

theorem compact_root_start (Is : List UpsInst) (q i : Nat) (D : URow)
    (hl : (inst Is i).post.length=32) :
    compactMsgs (compactGeneratedRow Is q (i,.w 3)) D B_ROOT true=
      [reduceMessage ([(inst Is i).tau+1]++(inst Is i).post)] := by
  rw [compact_root_send]
  have hsf : compactGeneratedRow Is q (i,.w 3) UpsV3.wt3=1:=rfl
  rw [hsf,show Fp.ofNat 1=1 from rfl]
  simp only [ite_true,if_pos rfl]
  have ht : compactGeneratedRow Is q (i,.w 3) UpsV3.tau=(inst Is i).tau%Algebra.P:=by
    simp [compactGeneratedRow,compactRowCell,UpsV3.tau,isSeg,segCell]
    exact Fp.toNat_ofNat _
  rw [ht]
  have hregs : (List.range 32).map (fun j=>compactGeneratedRow Is q (i,.w 3) (UpsV3.reg j))=
      (inst Is i).post.map (fun x=>x%Algebra.P) := by
    apply List.ext_getElem (by simp [hl])
    intro j hj hj'
    simp only [List.length_map,List.length_range] at hj
    simp only [List.getElem_map,List.getElem_range,compact_root_register Is q i j hj]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (hl ▸ hj),Option.getD_some]
  rw [hregs]
  simp [reduceMessage,List.map_map,Function.comp_def,Nat.mod_mod,Nat.add_mod]

theorem compact_root_row (Is : List UpsInst) (q i : Nat) (rk : RK) (D : URow)
    (hl : (inst Is i).post.length=32) :
    compactMsgs (compactGeneratedRow Is q (i,rk)) D B_ROOT true=
      if rk=.w 3 then [reduceMessage ([(inst Is i).tau+1]++(inst Is i).post)] else [] := by
  cases rk with
  | w t=>
    by_cases ht : t=3
    · subst t;simpa using compact_root_start Is q i D hl
    · have hs : compactGeneratedRow Is q (i,.w t) UpsV3.wt3=0 := by
        simp [compactGeneratedRow,compactRowCell,isSeg,UpsV3.wt3,wCell,ind,ht]
        rfl
      rw [compact_root_silent _ _ hs]
      simp [ht]
  | v p=>
    have hs : compactGeneratedRow Is q (i,.v p) UpsV3.wt3=0:=rfl
    rw [compact_root_silent _ _ hs]
    rfl
  | q k p=>
    have hs : compactGeneratedRow Is q (i,.q k p) UpsV3.wt3=0:=rfl
    rw [compact_root_silent _ _ hs]
    rfl

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
