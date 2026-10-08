import ZkFormal.NearV3.Rcpt.Candidates.UpsCounterPatch

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near Render.UpsGen

theorem instOk_walk_length (I : Render.UpsInst) (h : InstOk I) : 4≤I.walk.length := by
  by_cases hl : 4≤I.walk.length
  · exact hl
  · have hg : step I 3=default := by
      simp [step,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : I.walk.length≤3)]
    have hh:=h.walk.stepE 3 (by decide) (by decide) (by rw [hg];rfl)
    have hz:=hh.1
    rw [hg] at hz
    change (0:Nat)=16 at hz
    omega

def fourSteps (I : Render.UpsInst) : List WStep3 := List.ofFn (fun i : Fin 4=>step I i)

theorem fourSteps_take (I : Render.UpsInst) (h : 4≤I.walk.length) : fourSteps I=I.walk.take 4 := by
  apply List.ext_getElem
  · simp [fourSteps,List.length_take];omega
  · intro i hi hj
    have hi' : i<4 := by simpa [fourSteps] using hi
    have hl : i<I.walk.length := by omega
    simp only [fourSteps,List.getElem_ofFn,List.getElem_take]
    exact (List.getElem_eq_getD default).symm

def rankUpsList : List WStep3→List Render.UpsInst→List Render.UpsInst
  | _,[]=>[]
  | p,I::Is=>rankUps p I::rankUpsList (p++fourSteps I) Is

theorem rankUpsList_instOk : ∀(Is : List Render.UpsInst)(p : List WStep3),
    (∀I∈Is,InstOk I) → ∀J∈rankUpsList p Is,InstOk J
  | [],_,_,_,h=>by simp [rankUpsList] at h
  | I::Is,p,h,J,hJ=>by
    simp only [rankUpsList,List.mem_cons] at hJ
    rcases hJ with rfl|hJ
    · exact rankUps_instOk p I (h I (by simp))
    · exact rankUpsList_instOk Is _ (fun I hI=>h I (by simp [hI])) J hJ

theorem rankUpsList_parts : ∀(Is : List Render.UpsInst)(p : List WStep3),
    (∀I∈Is,NativePartFamily I) → ∀J∈rankUpsList p Is,NativePartFamily J
  | [],_,_,_,h=>by simp [rankUpsList] at h
  | I::Is,p,h,J,hJ=>by
    simp only [rankUpsList,List.mem_cons] at hJ
    rcases hJ with rfl|hJ
    · exact rankUps_parts p I (h I (by simp))
    · exact rankUpsList_parts Is _ (fun I hI=>h I (by simp [hI])) J hJ

theorem rankUps_fourSteps (p : List WStep3) (I : Render.UpsInst) (h : InstOk I) :
    fourSteps (rankUps p I)=rankSteps p (fourSteps I) := by
  rw [←rankSteps_ofFn]
  apply List.ext_getElem
  · simp [fourSteps]
  · intro i hi hj
    have hi' : i<4 := by simpa [fourSteps] using hi
    have hl : i<I.walk.length := by have hh:=instOk_walk_length I h;omega
    have ht : (fourSteps I).take i=I.walk.take i := by
      rw [fourSteps_take I (instOk_walk_length I h),List.take_take]
      simp [Nat.min_eq_left (by omega : i≤4)]
    simp only [fourSteps,List.getElem_ofFn,Fin.getElem_fin]
    change step (rankUps p I) i=rankWalkStep (p++(fourSteps I).take i) (step I i)
    rw [ht]
    simp only [rankUps,rankWalk,step,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hl,Option.getD_some,List.getElem?_eq_getElem hl,Fin.getElem_fin]

theorem ups_inventory_flat (Is : List Render.UpsInst) :
    (upsWalkInventory Is).flatMap (·.steps)=Is.flatMap fourSteps := by
  simp only [upsWalkInventory,List.flatMap_map]
  rfl

theorem rankUpsList_flatten : ∀(Is : List Render.UpsInst)(p : List WStep3),
    (∀I∈Is,InstOk I) → (rankUpsList p Is).flatMap fourSteps=rankSteps p (Is.flatMap fourSteps)
  | [],_,_=>rfl
  | I::Is,p,h=>by
    simp only [rankUpsList,List.flatMap_cons,rankUps_fourSteps p I (h I (by simp)),
      rankUpsList_flatten Is _ (fun I hI=>h I (by simp [hI])),rankSteps_append]

theorem rankUpsList_inventory (Is : List Render.UpsInst) (p : List WStep3)
    (h : ∀I∈Is,InstOk I) :
    (upsWalkInventory (rankUpsList p Is)).flatMap (·.steps)=
      (rankWalks p (upsWalkInventory Is)).flatMap (·.steps) := by
  rw [ups_inventory_flat,rankWalks_flatten,ups_inventory_flat,rankUpsList_flatten Is p h]

theorem rankUpsList_edge_traffic (Is : List Render.UpsInst) (h : ∀I∈Is,InstOk I) (sd : Bool) :
    edgeTraffic ((upsWalkInventory (rankUpsList [] Is)).flatMap (·.steps)) sd=
    completeCounterMessages (walkEdgeKeys (upsWalkInventory Is)) sd := by
  rw [rankUpsList_inventory Is [] h,edgeTraffic_flatten]
  exact ranked_walk_edges _ sd

theorem rankUpsList_bitmap_traffic (Is : List Render.UpsInst) (h : ∀I∈Is,InstOk I) (sd : Bool) :
    bitmapTraffic ((upsWalkInventory (rankUpsList [] Is)).flatMap (·.steps)) sd=
    completeCounterMessages (walkBmapKeys (upsWalkInventory Is)) sd := by
  rw [rankUpsList_inventory Is [] h,bitmapTraffic_flatten]
  exact ranked_walk_bmaps _ sd

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
