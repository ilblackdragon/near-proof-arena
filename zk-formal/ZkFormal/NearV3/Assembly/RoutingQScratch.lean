import ZkFormal.NearV3.Assembly.RoutingQCandidate

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/- Constant zero/one reduction only, keeping all remaining expressions intact. -/
def foldMul : Expr → Expr → Expr
  | .const 0,_ | _,.const 0 => .const 0
  | .const 1,b => b
  | a,.const 1 => a
  | a,b => .mul a b

def foldAdd : Expr → Expr → Expr
  | .const 0,b => b
  | a,.const 0 => a
  | a,b => .add a b

/- Specialize the one-hot current state; next-row cells stay symbolic. -/
def atState (state : Nat) : Expr → Expr
  | .col k false => if 4≤k ∧ k≤26 then .const (if k=state then 1 else 0) else .col k false
  | .mul a b => foldMul (atState state a) (atState state b)
  | .add a b => foldAdd (atState state a) (atState state b)
  | .neg a => match atState state a with | .const 0 => .const 0 | x => .neg x
  | e => e

def readsScratch (next : Bool) : Expr → Bool
  | .col k nx => nx==next && decide (xb 12≤k ∧ k≤xb 18)
  | .add a b | .mul a b => readsScratch next a || readsScratch next b
  | .neg a => readsScratch next a
  | _ => false

/- On receiver rows, the only constraints reading xb12..18 are their seven
existing boolean checks. This checks the entire active constraint list. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem receiver_scratch_constraints :
    (RcptV3.constraints.map (atState sV)).filter (readsScratch false)=
      (List.range 7).map (fun i=>bool (c (xb (12+i)))) := by decide

/- No receiver-row constraint reads those next-row scratch cells. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem receiver_next_scratch :
    (RcptV3.constraints.map (atState sV)).all (fun e=>!(readsScratch true e))=true := by decide

/- The length-field row preceding the first receiver row does not consume the
new scratch bits through next-row expressions. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem predecessor_next_scratch :
    (RcptV3.constraints.map (atState sVL)).all (fun e=>!(readsScratch true e))=true := by decide

/- No bus message or multiplicity expression directly reads the reused bits. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem interaction_scratch_free :
    (RcptV3.interactions.flatMap fun i=>i.msg++i.mult).all
      (fun e=>!(readsScratch false e) && !(readsScratch true e))=true := by decide

end ZkFormal.NearV3.Assembly.RoutingQCandidate
