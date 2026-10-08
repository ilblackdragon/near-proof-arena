import ZkFormal.NearV3.Candidates.ProcPriorVertical4Clock
import ZkFormal.NearV3.Candidates.ProcPriorRecordTrace
namespace ZkFormal.NearV3.Candidates.ProcPriorVertical4ClockTrace
open ZkFormal.Air ZkFormal.Algebra ProcPriorVertical4ClockCases ProcPriorVertical4Clock

/-- Marker equations are independent of all 23 overlaid data columns and of the
next row's last marker, which is not inspected by these window constraints. -/
theorem data_irrelevant (d dn : Nat→Fp) (s sn : Nat) (f l fn ln gf gl : Bool)
    (e : Expr) (he:e∈ProcPriorVertical4Linear.windows) :
    e.evalWith (ProcPriorCells.env (cell d s f l) (cell dn sn fn ln)
      (flag gf) (flag gl) (flag (!gl)))=e.evalWith (markerEnv s sn f l fn gf gl) := by
  simp only [ProcPriorVertical4Linear.windows,List.range_succ,List.range_zero,List.map_append,
    List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or,or_assoc] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals rfl

def trace (a b c : Nat) (data : Nat→Nat→Fp) : Trace Fp:=
  {log:=fun _=>22,
   cell:=fun _ j=>cell (data j) (stageAt a b c j) (firstAt a b c j) (lastAt a b c (2^22) j)}

theorem pub_zero (e : Expr) (he:e∈ProcPriorVertical4Linear.windows) : e.pubBound=0 := by
  have h:ProcPriorVertical4Linear.windows.all (fun e=>decide (e.pubBound=0))=true:=by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h e he)

theorem row_eval (a b c : Nat) (data : Nat→Nat→Fp) (tt j : Nat) (pub : List Fp)
    (e : Expr) (he:e∈ProcPriorVertical4Linear.windows) :
    e.eval (trace a b c data) tt j pub=e.evalWith
      (markerEnv (stageAt a b c j) (stageAt a b c ((j+1)%2^22))
        (firstAt a b c j) (lastAt a b c (2^22) j) (firstAt a b c ((j+1)%2^22))
        (decide (j=0)) (decide (j+1=2^22))) := by
  let en:=ProcPriorCells.env
    (cell (data j) (stageAt a b c j) (firstAt a b c j) (lastAt a b c (2^22) j))
    (cell (data ((j+1)%2^22)) (stageAt a b c ((j+1)%2^22))
      (firstAt a b c ((j+1)%2^22)) (lastAt a b c (2^22) ((j+1)%2^22)))
    (flag (decide (j=0))) (flag (decide (j+1=2^22))) (flag (!(decide (j+1=2^22))))
  have hh:rowEnv (trace a b c data) tt j pub={en with pub:=fun i=>pub.getD i 0} := by
    simp only [rowEnv,trace,Trace.height,en,ProcPriorCells.env,flag,decide_eq_true_eq]
    congr 1
    · funext col nx
      cases nx <;> rfl
    · by_cases h:j+1=2^22 <;> simp [h]
  change e.evalWith (rowEnv (trace a b c data) tt j pub)=_
  rw [hh,ProcPriorTrace.eval_pub e (pub_zero e he) en (fun i=>pub.getD i 0)]
  exact data_irrelevant _ _ _ _ _ _ _ _ _ _ e he

theorem constraints (a b c : Nat) (ha:0<a) (hab:a<b) (hbc:b<c) (hc:c<2^22)
    (data : Nat→Nat→Fp) (tt j : Nat) (hj:j<2^22) (pub : List Fp) :
    ∀e∈ProcPriorVertical4Linear.windows,e.eval (trace a b c data) tt j pub=0 := by
  intro e he
  rw [row_eval a b c data tt j pub e he]
  exact ProcPriorVertical4Clock.constraints a b c (2^22) j ha hab hbc hc hj e he
end ZkFormal.NearV3.Candidates.ProcPriorVertical4ClockTrace
