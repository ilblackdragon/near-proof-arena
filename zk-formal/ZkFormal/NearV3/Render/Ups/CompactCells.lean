import ZkFormal.NearV3.Render.Ups.CompactTraversal

namespace ZkFormal.NearV3.Render.UpsRelay
open UpsGen

theorem compactRecs_length (insts : List UpsInst) : (compactRecs insts).length=compactR insts := by
  have hm : (List.range insts.length).map (fun i=>(compactRecsI (inst insts i)).length)=
      insts.map (fun I=>(compactRecsI I).length) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp only [List.length_map] at hj
    simp only [List.getElem_map,List.getElem_range,inst,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj,Option.getD_some]
  simp only [compactRecs,List.length_flatMap,List.length_map,hm,compactR]

/-- UPB multiplicities count preceding reads in the compact physical row order. -/
def compactU (insts : List UpsInst) (q : Nat) : Nat :=
  (((compactRecs insts).take q).filter fun r=>rkey insts r==rkey insts ((compactRecs insts).getD q default)).length

def compactRowCell (insts : List UpsInst) (q : Nat) (r : Nat×RK) (x : Nat) : Int :=
  let I:=inst insts r.1
  if isSeg x then segCell I x else match r.2 with
  | .w t=>wCell I t x
  | .v p=>vCell I p x
  | .q k p=>qCell I k p (compactU insts q) x

/-- Isolated compact renderer, with one inactive padding row available. -/
def compactCell (insts : List UpsInst) (q x : Nat) : Int :=
  if q<compactR insts then compactRowCell insts q ((compactRecs insts).getD q default) x else 0

theorem compact_pad {insts : List UpsInst} {q : Nat} (h : compactR insts≤q) (x : Nat) :
    compactCell insts q x=0 := by simp [compactCell,show ¬q<compactR insts by omega]

theorem compact_mem_I {I : UpsInst} {r : RK} : r∈compactRecsI I ↔
    (∃ t,t<4 ∧ r=.w t) ∨ (∃ k p,k<nQ I ∧ p<(part I k).q.length ∧ r=.q k p) := by
  simp [compactRecsI,List.mem_flatMap,List.mem_map,List.mem_range,and_assoc,eq_comm]

theorem compact_mem {insts : List UpsInst} {r : Nat×RK} : r∈compactRecs insts ↔
    r.1<insts.length ∧ r.2∈compactRecsI (inst insts r.1) := by
  simp only [compactRecs,List.mem_flatMap,List.mem_range,List.mem_map]
  constructor
  · rintro ⟨i,hi,rk,hr,h⟩
    cases h
    exact ⟨hi,hr⟩
  · intro h
    exact ⟨r.1,h.1,r.2,h.2,by cases r; rfl⟩

theorem compact_get_mem {insts : List UpsInst} {q : Nat} (hq : q<compactR insts) :
    (compactRecs insts).getD q default∈compactRecs insts := by
  have hq' : q<(compactRecs insts).length := by rw [compactRecs_length]; exact hq
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hq',Option.getD_some]
  exact List.getElem_mem hq'

theorem compact_adjAt {insts : List UpsInst} (hi : ∀I∈insts,InstOk I)
    {q : Nat} (hq : q+1<compactR insts) :
    CompactAdj insts ((compactRecs insts).getD q default) ((compactRecs insts).getD (q+1) default) := by
  have hq' : q+1<(compactRecs insts).length := by rw [compactRecs_length]; exact hq
  have hh := (compactRecs_adj hi).get q hq'
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by omega : q<(compactRecs insts).length),
    List.getElem?_eq_getElem hq',Option.getD_some]
  exact hh

theorem compact_first {insts : List UpsInst} (hpos : 0<insts.length) :
    (compactRecs insts).getD 0 default=(0,.w 0) := by
  obtain ⟨m,hm⟩ : ∃m,insts.length=m+1 := ⟨insts.length-1,by omega⟩
  simp [compactRecs,hm,List.range_succ_eq_map,compactRecsI,List.getD_eq_getElem?_getD]

theorem compactR_pos {insts : List UpsInst} (hpos : 0<insts.length) : 0<compactR insts := by
  rw [←compactRecs_length]
  obtain ⟨m,hm⟩ : ∃m,insts.length=m+1 := ⟨insts.length-1,by omega⟩
  simp [compactRecs,hm,List.range_succ_eq_map,compactRecsI]
end ZkFormal.NearV3.Render.UpsRelay
