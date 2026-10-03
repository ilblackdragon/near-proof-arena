import ZkFormal.Sha.Stub.Fp

/-!
# ZkFormal.Sha.Stub.Air — local stand-in for lane L4's AIR DSL

Transcribed from DESIGN.md §5.1 so that lane L5 can be drafted before L4's
skeleton lands.  Port plan: replace `import ZkFormal.Sha.Stub.Air` by L4's
module and re-prove the handful of `eval_*` simp lemmas below against L4's
`Expr.eval`; nothing else in `ZkFormal.Sha` looks inside `Expr.eval`.

Assumptions about L4's semantics that the SHA proofs rely on (recorded in
docs/zk-formal/REQUESTS.md):
* `col c true` reads row `(r + 1) % 2^log` (cyclic next row);
* `isFirst` evaluates to `1` on row 0 and `0` elsewhere;
* `Holds` includes, for every table, every constraint evaluating to `0` on
  every row `r < 2^log`, and `log ≤ maxLog`.
-/

namespace ZkFormal.Sha.Air

open ZkFormal.Sha

inductive Expr where
  | const (c : Nat)
  | col (col : Nat) (next : Bool)
  | pub (i : Nat)
  | isFirst
  | isLast
  | isTransition
  | add (a b : Expr)
  | mul (a b : Expr)
  | neg (a : Expr)
  deriving Inhabited, Repr

structure Interaction where
  bus : Nat
  mult : Expr
  msg : List Expr
  send : Bool

structure Table where
  width : Nat
  constraints : List Expr
  interactions : List Interaction
  maxLog : Nat

structure Air where
  tables : List Table
  numBuses : Nat
  numPub : Nat

/-- `cell t r c` : table, row, column. -/
structure Trace where
  log : Nat → Nat
  cell : Nat → Nat → Nat → Fp

def Trace.height (tr : Trace) (t : Nat) : Nat := 2 ^ tr.log t

def Expr.eval : Expr → Trace → (t r : Nat) → (pub : List Fp) → Fp
  | .const c, _, _, _, _ => Fp.ofNat c
  | .col c nx, tr, t, r, _ => tr.cell t (if nx then (r + 1) % tr.height t else r) c
  | .pub i, _, _, _, pv => pv.getD i 0
  | .isFirst, _, _, r, _ => if r = 0 then 1 else 0
  | .isLast, tr, t, r, _ => if r + 1 = tr.height t then 1 else 0
  | .isTransition, tr, t, r, _ => if r + 1 = tr.height t then 0 else 1
  | .add a b, tr, t, r, pv => a.eval tr t r pv + b.eval tr t r pv
  | .mul a b, tr, t, r, pv => a.eval tr t r pv * b.eval tr t r pv
  | .neg a, tr, t, r, pv => -(a.eval tr t r pv)

/-- Local constraints of one table: every constraint vanishes on every row. -/
def TableHolds (T : Table) (pub : List Fp) (tr : Trace) (t : Nat) : Prop :=
  tr.log t ≤ T.maxLog ∧ ∀ r, r < tr.height t → ∀ c ∈ T.constraints, c.eval tr t r pub = 0

/-- Total multiplicity with which table `t` emits message `v` on bus `b` in
direction `send`. -/
def tableCount (T : Table) (tr : Trace) (t : Nat) (pub : List Fp) (b : Nat) (send : Bool)
    (v : List Fp) : Nat :=
  ((List.range (tr.height t)).map fun r =>
    ((T.interactions.filter fun i => i.bus == b && i.send == send).map fun i =>
      if (i.msg.map fun e => e.eval tr t r pub) = v then (i.mult.eval tr t r pub).val else 0).sum).sum

def busCount (A : Air) (tr : Trace) (pub : List Fp) (b : Nat) (send : Bool) (v : List Fp) : Nat :=
  ((List.range A.tables.length).map fun t =>
    tableCount (A.tables.getD t ⟨0, [], [], 0⟩) tr t pub b send v).sum

/-- Semantic predicate (stub): local constraints of every table, plus
multiset balance of every bus with multiplicities read as naturals. -/
def Holds (A : Air) (pub : List Fp) (tr : Trace) : Prop :=
  (∀ t, t < A.tables.length → TableHolds (A.tables.getD t ⟨0, [], [], 0⟩) pub tr t) ∧
  ∀ b v, busCount A tr pub b true v = busCount A tr pub b false v

/-! ## Evaluation lemmas (the only facts about `Expr.eval` used downstream) -/

section
variable (tr : Trace) (t r : Nat) (pub : List Fp)

@[simp] theorem eval_const (c : Nat) : (Expr.const c).eval tr t r pub = Fp.ofNat c := rfl
@[simp] theorem eval_col (c : Nat) :
    (Expr.col c false).eval tr t r pub = tr.cell t r c := rfl
@[simp] theorem eval_colNext (c : Nat) :
    (Expr.col c true).eval tr t r pub = tr.cell t ((r + 1) % tr.height t) c := rfl
@[simp] theorem eval_add (a b : Expr) :
    (Expr.add a b).eval tr t r pub = a.eval tr t r pub + b.eval tr t r pub := rfl
@[simp] theorem eval_mul (a b : Expr) :
    (Expr.mul a b).eval tr t r pub = a.eval tr t r pub * b.eval tr t r pub := rfl
@[simp] theorem eval_neg (a : Expr) :
    (Expr.neg a).eval tr t r pub = -(a.eval tr t r pub) := rfl
@[simp] theorem eval_isFirst :
    Expr.isFirst.eval tr t r pub = if r = 0 then 1 else 0 := rfl

end

end ZkFormal.Sha.Air
