import ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonTraffic
import ZkFormal.NearV3.Candidates.ProcPriorOverlayTrafficEval
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched.Complete
open ProcPriorNativeMemory ProcPriorCells ProcPriorComparisonRequests ProcPriorVertical4Linear

theorem row_env (xs : List Tagged) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorMemoryTable.interactions 67 68 69) (trace xs) t r pub 69 true=
      trafficWith (ProcPriorMemoryTable.interactions 67 68 69)
        (env (cells xs r) (cells xs ((r+1)%2^22))
          (if r=0 then 1 else 0) (if r+1=2^22 then 1 else 0) (if r+1=2^22 then 0 else 1)) 69 true := by
  rw [traffic_row]
  apply ProcPriorOverlayTrafficEval.traffic_congr
  intro a ha e he
  have hall:(ProcPriorMemoryTable.interactions 67 68 69).all
      (fun a=>(a.mult++a.msg).all (fun e=>decide (e.pubBound=0)))=true:=by decide +kernel
  exact row_eval xs t r pub e
    (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hall a ha) e he))

theorem pair (xs : List Tagged) (t r : Nat) (pub : List Fp) (a b : Tagged)
    (ha:xs[r]?=some a) (hb:xs[r+1]?=some b) (hr:r+1<2^22) :
    rowTraffic (ProcPriorMemoryTable.interactions 67 68 69) (trace xs) t r pub 69 true=
      (memoryPair a b).map cmpMsg := by
  rw [row_env,Nat.mod_eq_of_lt hr,cells_some xs r a ha,cells_some xs (r+1) b hb]
  simp only [nextSame,nextInverse,hb,ite_eq_right (show r+1≠2^22 by omega)]
  exact ProcPriorMemoryComparisonTraffic.pair a b _ _ _

theorem quiet (cur nxt : Nat→Fp) (fi la tr : Fp)
    (hq:cur ProcPriorMemoryTable.act=0 ∨ nxt ProcPriorMemoryTable.act=0) :
    trafficWith (ProcPriorMemoryTable.interactions 67 68 69) (env cur nxt fi la tr) 69 true=[] := by
  rcases hq with h|h
  all_goals simp only [trafficWith,ProcPriorMemoryTable.interactions,List.flatMap_cons,List.flatMap_nil]
  all_goals simp [multWith,Expr.evalWith,env,c,n,k,ProcPriorMemoryTable.adjacent,
    ProcPriorMemoryTable.notE,sub,h]
  all_goals simp only [show (0:Fp)*nxt ProcPriorMemoryTable.act=0 from by grind,
    show cur ProcPriorMemoryTable.act*(0:Fp)=0 from by grind,
    show ∀x:Fp,(0:Fp)*x=0 from by intros;grind,
    show (0:Fp)≠1 from by decide +kernel,ite_false,List.replicate_zero,List.append_nil]
  all_goals simp

theorem row (xs : List Tagged) (hcap:xs.length<2^22) (t r : Nat) (pub : List Fp) (hr:r<2^22) :
    rowTraffic (ProcPriorMemoryTable.interactions 67 68 69) (trace xs) t r pub 69 true=
      match xs[r]?,xs[r+1]? with
      | some a,some b=>(memoryPair a b).map cmpMsg
      | _,_=>[] := by
  cases ha:xs[r]? with
  | none=>
    rw [row_env,cells_none xs r ha]
    apply quiet
    exact Or.inl rfl
  | some a=>
    have hra:r<xs.length:=(List.getElem?_eq_some_iff.mp ha).1
    have hnext:r+1<2^22:=by omega
    cases hb:xs[r+1]? with
    | some b=>exact pair xs t r pub a b ha hb hnext
    | none=>
      rw [row_env,Nat.mod_eq_of_lt hnext,cells_none xs (r+1) hb]
      apply quiet
      exact Or.inr rfl
end ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonRows
