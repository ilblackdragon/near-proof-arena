import ZkFormal.NearV3.Render.Ups.CompactFrame
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near.Render UpsGen

theorem compact_recs_last {insts : List UpsInst} (hpos : 0<insts.length)
    (hi : ∀I∈insts,InstOk I) :
    (compactRecs insts).getLast?=some (insts.length-1,lastRK (inst insts (insts.length-1))) := by
  unfold compactRecs
  obtain ⟨m,hm⟩ : ∃m,insts.length=m+1 := ⟨insts.length-1,by omega⟩
  rw [hm,List.range_succ,List.flatMap_append,List.getLast?_append]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.getLast?_map]
  rw [compactRecsI_last (hi _ (inst_mem (by omega : m<insts.length)))]
  simp

theorem compact_lastAt {insts : List UpsInst} (hpos : 0<insts.length)
    (hi : ∀I∈insts,InstOk I) :
    (compactRecs insts).getD (compactR insts-1) default=
      (insts.length-1,lastRK (inst insts (insts.length-1))) := by
  have h:=compact_recs_last hpos hi
  rw [List.getLast?_eq_getElem?,compactRecs_length] at h
  rw [List.getD_eq_getElem?_getD,h]; rfl

theorem compact_nextRow {insts : List UpsInst} (hpos : 0<insts.length)
    (hi : ∀I∈insts,InstOk I) {q i : Nat} {rk rk' : RK} (hq : q<compactR insts)
    (hr : (compactRecs insts).getD q default=(i,rk))
    (hn : compactNext (inst insts i) rk=some rk') (x : Nat) :
    compactNextCell insts q x=compactRowCell insts (q+1) (i,rk') x := by
  have h1 : q+1<compactR insts := by
    apply Classical.byContradiction; intro h
    have hh:=compact_lastAt hpos hi
    rw [show compactR insts-1=q by omega,hr] at hh
    cases hh
    rw [compactNext_last (hi _ (inst_mem (by omega)))] at hn
    cases hn
  have ha:=compact_adjAt hi h1
  rw [hr] at ha
  rcases ha with ⟨h,h'⟩|⟨h,-⟩
  · simp only at h h'
    rw [hn] at h
    have e:=Option.some.inj h
    have e2 : (compactRecs insts).getD (q+1) default=(i,rk') := by
      apply Prod.ext h' e.symm
    simp only [compactNextCell,compactCell,h1,ite_true,e2]
  · simp only at h; rw [hn] at h; cases h

theorem compact_nextLastAll {insts : List UpsInst} (hi : ∀I∈insts,InstOk I)
    {q i : Nat} {rk : RK} (hr : (compactRecs insts).getD q default=(i,rk))
    (hn : compactNext (inst insts i) rk=none) :
    (∀x,compactNextCell insts q x=0) ∨
    (∀x,compactNextCell insts q x=compactRowCell insts (q+1) (i+1,.w 0) x) := by
  by_cases h1 : q+1<compactR insts
  · right
    have ha:=compact_adjAt hi h1
    rw [hr] at ha
    rcases ha with ⟨h,-⟩|⟨-,h⟩
    · simp only at h; rw [hn] at h; cases h
    · intro x; simp only [compactNextCell,compactCell,h1,ite_true,h]
  · left; intro x; simp [compactNextCell,compactCell,h1]

theorem compact_q_ne0 {insts : List UpsInst} (hpos : 0<insts.length)
    {q i : Nat} {rk : RK} (hr : (compactRecs insts).getD q default=(i,rk))
    (hrk : rk≠.w 0) : q≠0 := by
  rintro rfl
  rw [compact_first hpos] at hr
  cases hr; exact hrk rfl
end ZkFormal.NearV3.Render.UpsRelay
