import ZkFormal.Sha.Table
import ZkFormal.Size.Model
import ZkFormal.Algebra.Fp

/-! Isolated carry-pair packing candidate. Every original constraint is retained
under exact expression substitution. This is not an active SHA table change. -/
namespace ZkFormal.NearV3.Candidates.ShaCarryPairs
open ZkFormal.Air ZkFormal.Sha.Table.E
set_option maxRecDepth 32768

/-- Low bit on {0,1,2,3}; inverse of3 in BabyBear. -/
def low (x : Expr) : Expr :=
  smul 1342177281 (.add (sub (smul 2 (.mul (.mul x x) x)) (smul 9 (.mul x x))) (smul 10 x))
/-- High bit on {0,1,2,3}; inverse of6 in BabyBear. -/
def high (x : Expr) : Expr :=
  smul 1677721601 (.mul (.mul x (sub x (k 1))) (sub (k 7) (smul 2 x)))

/-- Carry bits384..455 are24 triples; each becomes a low-pair digit and high bit. -/
def column (i : Nat) (nx : Bool) : Expr :=
  if i<384 then .col i nx
  else if i<456 then
    let j := i-384
    let x := Expr.col (384+2*(j/3)) nx
    if j%3=0 then low x
    else if j%3=1 then high x
    else .col (385+2*(j/3)) nx
  else .col (i-24) nx

def expression : Expr → Expr
  | .col i nx => column i nx
  | .add a b => .add (expression a) (expression b)
  | .mul a b => .mul (expression a) (expression b)
  | .neg a => .neg (expression a)
  | e => e

def interaction (i : Interaction) : Interaction :=
  {i with mult:=i.mult.map expression,msg:=i.msg.map expression}

def table (bb bd : Nat) : Air.Table :=
  {width:=520,constraints:=ZkFormal.Sha.Table.constraints.map expression,
   interactions:=(ZkFormal.Sha.Table.interactions bb bd).map interaction,maxLog:=22}

/-- Full expression semantics, over any carrier, in the decoded original environment. -/
theorem expression_eval {R : Type} (env : Env R) (e : Expr) :
    (expression e).evalWith env =
      e.evalWith {env with col:=fun i nx => (column i nx).evalWith env} := by
  induction e <;> simp_all [expression,Expr.evalWith]

/-- Sound local constraint transport; no carry-range or digest assumption. -/
theorem constraints_decode {R : Type} (env : Env R) (zero : R)
    (h : ∀e∈(table 0 1).constraints,e.evalWith env=zero) :
    ∀e∈ZkFormal.Sha.Table.constraints,
      e.evalWith {env with col:=fun i nx => (column i nx).evalWith env}=zero := by
  intro e he
  rw [← expression_eval]
  exact h (expression e) (List.mem_map.mpr ⟨e,he,rfl⟩)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem shape : ZkFormal.Size.shapeOf 2 (table 0 1)=⟨520,9,5,9,22⟩ := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem table_wf : (table 0 1).wf ⟨[table 0 1],2,0⟩ 8=true := by decide +kernel
open ZkFormal.Algebra

def scalarEnv (x : Fp) : Env Fp :=
  ⟨(fun n => n), (·+·), (·*·), Neg.neg, (fun _ _ => x), (fun _ => 0), 0, 0, 0⟩
def decodeLow (x : Fp) : Fp := (low (.col 0 false)).evalWith (scalarEnv x)
def decodeHigh (x : Fp) : Fp := (high (.col 0 false)).evalWith (scalarEnv x)

/-- Honest encoding of every possible low carry-bit pair is lossless. -/
theorem pair_decode (a b : Fp) (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) :
    decodeLow (a+2*b)=a ∧ decodeHigh (a+2*b)=b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide +kernel

end ZkFormal.NearV3.Candidates.ShaCarryPairs
