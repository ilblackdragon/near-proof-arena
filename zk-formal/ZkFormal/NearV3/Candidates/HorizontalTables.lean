import ZkFormal.NearV3.Candidates.PackedMerkleFamily

/-! Horizontal fusion of independent tables. Only equal-height physical traces
can be projected/assembled directly; padding completeness is a separate obligation. -/
namespace ZkFormal.NearV3.Candidates.HorizontalTables
open ZkFormal.Air ZkFormal.Size

def expression (off : Nat) : Expr → Expr
  | .col i nx => .col (off+i) nx
  | .add a b => .add (expression off a) (expression off b)
  | .mul a b => .mul (expression off a) (expression off b)
  | .neg a => .neg (expression off a)
  | e => e

def interaction (off : Nat) (i : Interaction) : Interaction :=
  {i with mult:=i.mult.map (expression off),msg:=i.msg.map (expression off)}

def shifted (off : Nat) (t : Air.Table) : Air.Table :=
  {t with
    constraints:=t.constraints.map (expression off),
    interactions:=t.interactions.map (interaction off)}

def layout (off : Nat) : List Air.Table → List Air.Table
  | [] => []
  | t::ts => shifted off t :: layout (off+t.width) ts

def fuse (ts : List Air.Table) : Air.Table :=
  {width:=(ts.map (·.width)).sum,
   constraints:=(layout 0 ts).flatMap (·.constraints),
   interactions:=(layout 0 ts).flatMap (·.interactions),maxLog:=22}

def selected : List Air.Table := (PackedMerkleFamily.tables 4).filter (fun t => t.maxLog=22)
def rest : List Air.Table := (PackedMerkleFamily.tables 4).filter (fun t => t.maxLog != 22)
def tables : List Air.Table := fuse selected :: rest
def air : Air := ⟨tables,67,202⟩
def bytes (g : Nat) : Nat := sizeOfWeq (ZkFormal.V2.G.pg g) (tables.map (shapeOf g))

theorem actual_model (g : Nat) : sizeMaxDedup air (ZkFormal.V2.G.pg g)=bytes g :=
  sizeMaxDedup_eq_model air (ZkFormal.V2.G.pg g)

theorem expression_eval {R : Type} (env : Env R) (off : Nat) (e : Expr) :
    (expression off e).evalWith env=e.evalWith {env with col:=fun i nx => env.col (off+i) nx} := by
  induction e <;> simp_all [expression,Expr.evalWith]
end ZkFormal.NearV3.Candidates.HorizontalTables
