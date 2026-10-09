import ZkFormal.NearV3.Candidates.ShaCarryPairs

/-! Second isolated exact-substitution candidate: pack the16 round-selector
bits into8 base-four digits, in addition to the24 carry-pair savings; S/D stay Boolean. -/
namespace ZkFormal.NearV3.Candidates.ShaCarryKinds
open ZkFormal.Air
set_option maxRecDepth 32768

/-- After carry packing, original round columns502..517 occupy478..493. -/
def column (i : Nat) (nx : Bool) : Expr :=
  if i<478 then .col i nx
  else if i<494 then
    let j:=i-478
    let x:=Expr.col (478+j/2) nx
    if j%2=0 then ShaCarryPairs.low x else ShaCarryPairs.high x
  else .col (i-8) nx

def expression : Expr → Expr
  | .col i nx => column i nx
  | .add a b => .add (expression a) (expression b)
  | .mul a b => .mul (expression a) (expression b)
  | .neg a => .neg (expression a)
  | e => e

def interaction (i : Interaction) : Interaction :=
  {i with mult:=i.mult.map expression,msg:=i.msg.map expression}

def table (bb bd : Nat) : Air.Table :=
  {width:=512,constraints:=(ShaCarryPairs.table bb bd).constraints.map expression,
   interactions:=(ShaCarryPairs.table bb bd).interactions.map interaction,maxLog:=22}

theorem expression_eval {R : Type} (env : Env R) (e : Expr) :
    (expression e).evalWith env =
      e.evalWith {env with col:=fun i nx => (column i nx).evalWith env} := by
  induction e <;> simp_all [expression,Expr.evalWith]

/-- Direct semantics in the original544-column SHA environment. -/
theorem original_eval {R : Type} (env : Env R) (e : Expr) :
    (expression (ShaCarryPairs.expression e)).evalWith env =
      e.evalWith {env with col:=fun i nx =>
        (expression (ShaCarryPairs.column i nx)).evalWith env} := by
  rw [expression_eval,ShaCarryPairs.expression_eval]
  congr 1
  congr 1
  funext i nx
  exact (expression_eval env (ShaCarryPairs.column i nx)).symm

/-- Every accepted candidate constraint implies the corresponding original
constraint in the decoded environment. -/
theorem constraints_decode {R : Type} (env : Env R) (zero : R)
    (h : ∀e∈(table 0 1).constraints,e.evalWith env=zero) :
    ∀e∈ZkFormal.Sha.Table.constraints,
      e.evalWith {env with col:=fun i nx =>
        (expression (ShaCarryPairs.column i nx)).evalWith env}=zero := by
  intro e he
  rw [← original_eval]
  apply h
  exact List.mem_map.mpr ⟨ShaCarryPairs.expression e,
    List.mem_map.mpr ⟨e,he,rfl⟩,rfl⟩

/-- Actual bus-message and multiplicity evaluations are preserved together. -/
theorem interaction_eval {R : Type} (env : Env R) (i : Interaction) :
    let env0 := {env with col:=fun j nx =>
      (expression (ShaCarryPairs.column j nx)).evalWith env}
    ((interaction (ShaCarryPairs.interaction i)).mult.map (Expr.evalWith env),
     (interaction (ShaCarryPairs.interaction i)).msg.map (Expr.evalWith env)) =
    (i.mult.map (Expr.evalWith env0),i.msg.map (Expr.evalWith env0)) := by
  simp only [interaction,ShaCarryPairs.interaction,List.map_map]
  simp only [Function.comp_def,original_eval]

set_option maxHeartbeats 4000000 in
theorem shape : ZkFormal.Size.shapeOf 2 (table 0 1)=⟨512,9,5,9,22⟩ := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem table_wf : (table 0 1).wf ⟨[table 0 1],2,0⟩ 8=true := by decide +kernel
end ZkFormal.NearV3.Candidates.ShaCarryKinds
