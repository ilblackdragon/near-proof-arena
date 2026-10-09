import ZkFormal.NearV3.Rcpt.Candidates.WalkRequestInventory

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Algebra

def rankWalk (previous : List WStep3) (w : WalkR) : WalkR :=
  {w with steps:=List.ofFn (fun i : Fin w.steps.length=>
    rankWalkStep (previous++w.steps.take i) w.steps[i])}

def rankWalks : List WStep3→List WalkR→List WalkR
  | _,[]=>[]
  | previous,w::ws=>rankWalk previous w::rankWalks (previous++w.steps) ws

theorem rankWalk_length (previous : List WStep3) (w : WalkR) :
    (rankWalk previous w).steps.length=w.steps.length := List.length_ofFn

theorem rankWalk_at (previous : List WStep3) (w : WalkR) (i : Nat) (hi : i<w.steps.length) :
    (rankWalk previous w).steps[i]'(by simpa [rankWalk_length] using hi)=
      rankWalkStep (previous++w.steps.take i) w.steps[i] := by
  simp [rankWalk]

def stepShape (st : WStep3) := (st.mode,st.sym,st.e,st.bm,st.hv)

theorem rankWalk_shape (previous : List WStep3) (w : WalkR) (i : Nat) :
    stepShape ((rankWalk previous w).step i)=stepShape (w.step i) := by
  by_cases hi : i<w.steps.length
  · simp [WalkR.step,rankWalk,List.getD_eq_getElem?_getD,hi,stepShape,rankWalkStep]
  · simp [WalkR.step,rankWalk,List.getD_eq_getElem?_getD,hi,List.getElem?_eq_none (Nat.le_of_not_lt hi)]

theorem rankWalk_rows (previous : List WStep3) (w : WalkR)
    (h : ∀i (hi : i<w.steps.length),StepOk w.steps[i] (i+1==w.steps.length)) :
    ∀i (hi : i<(rankWalk previous w).steps.length),
      StepOk (rankWalk previous w).steps[i] (i+1==(rankWalk previous w).steps.length) := by
  intro i hi
  have ho : i<w.steps.length := by simpa [rankWalk_length] using hi
  rw [rankWalk_at previous w i ho,rankWalk_length]
  exact rankWalkStep_ok _ _ _ (h i ho)

theorem rankWalk_counter_bound (previous : List WStep3) (w : WalkR) (i : Nat)
    (hi : i<w.steps.length) :
    ((rankWalk previous w).step i).u<previous.length+w.steps.length ∧
    ((rankWalk previous w).step i).ub<previous.length+w.steps.length := by
  have hb:=rankWalkStep_bounds (previous++w.steps.take i) w.steps[i]
  have hg : (rankWalk previous w).step i=rankWalkStep (previous++w.steps.take i) w.steps[i] := by
    simp [WalkR.step,rankWalk,List.getD_eq_getElem?_getD,hi]
  rw [hg]
  simp only [List.length_append,List.length_take] at hb
  omega

theorem rankWalks_rows : ∀(ws : List WalkR)(previous : List WStep3),
    ((rankWalks previous ws).flatMap (·.steps)).length=(ws.flatMap (·.steps)).length
  | [],_=>rfl
  | w::ws,previous=>by simp [rankWalks,rankWalk_length,rankWalks_rows ws]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
