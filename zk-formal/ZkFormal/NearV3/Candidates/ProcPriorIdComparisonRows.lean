import ZkFormal.NearV3.Candidates.ProcPriorIdComparisonTraffic
namespace ZkFormal.NearV3.Candidates.ProcPriorIdComparisonRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched.Complete
open ProcIdTaggedCells ProcPriorCells ProcPriorComparisonRequests ProcPriorVertical4Linear

theorem row_env (xs : List Tagged) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorIdTable.interactions 70 71 72 69) (ProcIdTaggedTrace.trace xs) t r pub 69 true=
      trafficWith (ProcPriorIdTable.interactions 70 71 72 69)
        (env (ProcIdTaggedTrace.cell xs r) (ProcIdTaggedTrace.cell xs ((r+1)%2^22))
          (if r=0 then 1 else 0) (if r+1=2^22 then 1 else 0) (if r+1=2^22 then 0 else 1)) 69 true := by
  rw [traffic_row]
  apply ProcPriorOverlayTrafficEval.traffic_congr
  intro a ha e he
  have hall:(ProcPriorIdTable.interactions 70 71 72 69).all
      (fun a=>(a.mult++a.msg).all (fun e=>decide (e.pubBound=0)))=true:=by decide +kernel
  exact ProcIdTaggedTrace.row_eval xs t r pub e
    (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hall a ha) e he))

theorem quiet (cur nxt : Nat→Fp) (fi la tr : Fp)
    (hq:cur 0=0 ∨ nxt 0=0) (hg:cur 16=0 ∧ cur 17=0 ∧ cur 19=0) :
    trafficWith (ProcPriorIdTable.interactions 70 71 72 69) (env cur nxt fi la tr) 69 true=[] := by
  rcases hq with h|h
  all_goals simp [trafficWith,ProcPriorIdTable.interactions,multWith,Expr.evalWith,
    env,c,n,k,ProcPriorIdTable.adjacent,ProcPriorIdTable.act,
    ProcPriorIdTable.gTop,ProcPriorIdTable.gMid,ProcPriorIdTable.gPublic,h,hg.1,hg.2.1,hg.2.2]
  all_goals simp only [show (0:Fp)*nxt 0=0 from by grind,
    show cur 0*(0:Fp)=0 from by grind,show (0:Fp)≠1 from by decide +kernel,
    ite_false,List.replicate_zero]
  all_goals simp

theorem row (xs : List Tagged) (hcap:xs.length<2^22) (t r : Nat) (pub : List Fp) (hr:r<2^22) :
    rowTraffic (ProcPriorIdTable.interactions 70 71 72 69) (ProcIdTaggedTrace.trace xs) t r pub 69 true=
      (ProcPriorComparisonEnumeration.atRow idPair xs r).map cmpMsg := by
  unfold ProcPriorComparisonEnumeration.atRow
  cases ha:xs[r]? with
  | none=>
    rw [row_env,ProcIdTaggedTrace.padding xs r (List.getElem?_eq_none_iff.mp ha)]
    exact quiet _ _ _ _ _ (Or.inl rfl) ⟨rfl,rfl,rfl⟩
  | some a=>
    have hra:r<xs.length:=(List.getElem?_eq_some_iff.mp ha).1
    have hnext:r+1<2^22:=by omega
    cases hb:xs[r+1]? with
    | some b=>
      rw [row_env,Nat.mod_eq_of_lt hnext,ProcIdTaggedTrace.cell_some xs r a ha,
        ProcIdTaggedTrace.cell_some xs (r+1) b hb,hb]
      exact ProcPriorIdComparisonTraffic.pair a b _ _ _ _
    | none=>
      rw [row_env,Nat.mod_eq_of_lt hnext,ProcIdTaggedTrace.cell_some xs r a ha,
        ProcIdTaggedTrace.padding xs (r+1) (List.getElem?_eq_none_iff.mp hb),hb]
      apply quiet _ _ _ _ _ (Or.inr rfl)
      simp [cells,ProcPriorIdCells.cells,ProcPriorIdCells.sameTop,ProcPriorIdCells.eqLimb,
        ProcPriorIdCells.gateMid,ProcPriorIdCells.gateAll,bit]
end ZkFormal.NearV3.Candidates.ProcPriorIdComparisonRows
