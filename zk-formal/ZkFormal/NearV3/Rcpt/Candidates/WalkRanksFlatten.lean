import ZkFormal.NearV3.Rcpt.Candidates.WalkRanksWf

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

def rankSteps : List WStep3→List WStep3→List WStep3
  | _,[]=>[]
  | p,s::ss=>rankWalkStep p s::rankSteps (p++[s]) ss

theorem rankSteps_ofFn (p : List WStep3) (ss : List WStep3) :
    List.ofFn (fun i : Fin ss.length=>rankWalkStep (p++ss.take i) ss[i])=rankSteps p ss := by
  induction ss generalizing p with
  | nil => simp [rankSteps]
  | cons s ss ih =>
    rw [List.ofFn_succ]
    simp only [Fin.val_zero,List.take_zero,List.append_nil,List.getElem_cons_zero,
      Fin.val_succ,List.take_succ_cons,List.getElem_cons_succ,rankSteps]
    congr 1
    rw [←ih (p++[s])]
    congr 1
    funext i
    simp [List.append_assoc]

theorem rankSteps_append (p xs ys : List WStep3) :
    rankSteps p (xs++ys)=rankSteps p xs++rankSteps (p++xs) ys := by
  induction xs generalizing p with
  | nil => simp [rankSteps]
  | cons s xs ih => simp [rankSteps,ih,List.append_assoc]

theorem rankWalk_steps (p : List WStep3) (w : WalkR) :
    (rankWalk p w).steps=rankSteps p w.steps := rankSteps_ofFn p w.steps

theorem rankWalks_flatten (p : List WStep3) (ws : List WalkR) :
    (rankWalks p ws).flatMap (·.steps)=rankSteps p (ws.flatMap (·.steps)) := by
  induction ws generalizing p with
  | nil => rfl
  | cons w ws ih => simp [rankWalks,rankWalk_steps,ih,rankSteps_append]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
