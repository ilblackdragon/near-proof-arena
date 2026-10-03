/-!
# ZkFormal.Air.Basic — the AIR DSL (lane L4, DESIGN.md §5.1)

The AIR is a Lean value and the single source of truth (DESIGN.md decision B):
the deployed verifier evaluates constraints from it, the soundness theorem is
stated about it (`Holds`), and the Rust prover consumes its export
(`ZkFormal.Air.Export`, format in `docs/zk-formal/FORMATS.md`).

## Semantics, in one paragraph

An `Air` is a list of tables.  A `Trace` gives every table `t` a height
`2^(log t)` and a cell value `cell t r c` (table, row, column).  A constraint
is an `Expr` that must evaluate to `0` on **every** row `r < 2^(log t)` of its
table; `col c true` reads row `(r+1) mod 2^(log t)` (cyclic), and the three
selectors are `0/1`-valued: `isFirst = [r = 0]`, `isLast = [r = 2^log - 1]`,
`isTransition = 1 - isLast`.  (Those are the values on the trace domain of the
unique interpolants of degree `< 2^log`; the verifier evaluates the
interpolants out of domain in closed form.)  Each table also carries
*interactions* on numbered buses: on every row, interaction `i` sends
(`send = true`) or receives (`send = false`) the message `i.msg` (a list of
field elements) with multiplicity `Σₖ bₖ·2^k`, where `i.mult = [b₀, b₁, …]`
are its multiplicity *bits*; every bit must evaluate to `0` or `1`.  A bus
balances iff, for every message `m`, the total multiplicity with which `m` is
sent equals the total with which it is received (exact multiset equality over
the naturals, no wrap-around).

`Holds A pub tr` is the conjunction of: heights in `[2, 2^maxLog]`, all
constraints on all rows, booleanity of the multiplicity bits, and balance of
every bus.  No challenges appear; the IOP (lane L3) proves that the protocol's
grand-product argument enforces exactly this predicate.

## Deviation from the DESIGN.md §5.1 sketch

`Interaction.mult : List Expr` (bits, least significant first) instead of a
single `Expr`.  A grand product needs `(γ - fp)^m` with `m` a natural, and
the only polynomial way to raise to a witness-dependent natural power is
bit by bit; making the bits part of the AIR value means `Holds` reads the
multiplicity exactly as the protocol does.  A 0/1 selector `s` is `[s]`; the
constant multiplicity one is `[.const 1]`; `[]` is multiplicity zero.

The DSL is generic in the field `F` (any `Lean.Grind.CommRing`): the trace
lives in the base field (BabyBear, lane L1) and the verifier evaluates the same
expressions over the extension `K` at the out-of-domain point, through
`Expr.evalWith`.
-/

namespace ZkFormal.Air

/-- Constraint and message expressions. -/
inductive Expr where
  /-- The constant `c` (read in the field: `c mod p`). -/
  | const (c : Nat)
  /-- Column `col` of the current row (`next = false`) or of the next row
  (`next = true`, cyclically). -/
  | col (col : Nat) (next : Bool)
  /-- Public input `i` (`0` when out of range). -/
  | pub (i : Nat)
  | isFirst
  | isLast
  | isTransition
  | add (a b : Expr)
  | mul (a b : Expr)
  | neg (a : Expr)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A bus interaction of a table: on every row, send or receive `msg` with
multiplicity `Σₖ mult[k]·2^k` (bits, least significant first). -/
structure Interaction where
  bus : Nat
  mult : List Expr
  msg : List Expr
  send : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One table: its width (number of base-field columns), its constraints
(each must vanish on every row), its interactions, and the maximal
`log₂` height the protocol accepts for it. -/
structure Table where
  width : Nat
  constraints : List Expr
  interactions : List Interaction
  maxLog : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An AIR: tables, number of buses, number of public inputs. -/
structure Air where
  tables : List Table
  numBuses : Nat
  numPub : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A trace over the field `F`: `log t` is the `log₂` height of table `t`,
`cell t r c` the value of column `c` of row `r` of table `t`. -/
structure Trace (F : Type) where
  log : Nat → Nat
  cell : Nat → Nat → Nat → F

/-! ## Evaluation -/

/-- Everything an expression can read, over an arbitrary carrier `R`
(the base field on the trace; the extension field out of domain). -/
structure Env (R : Type) where
  ofNat : Nat → R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  /-- `col c next` -/
  col : Nat → Bool → R
  /-- `pub i` -/
  pub : Nat → R
  isFirst : R
  isLast : R
  isTransition : R

/-- Evaluate an expression in an environment. -/
def Expr.evalWith {R : Type} (env : Env R) : Expr → R
  | .const c => env.ofNat c
  | .col c nx => env.col c nx
  | .pub i => env.pub i
  | .isFirst => env.isFirst
  | .isLast => env.isLast
  | .isTransition => env.isTransition
  | .add a b => env.add (a.evalWith env) (b.evalWith env)
  | .mul a b => env.mul (a.evalWith env) (b.evalWith env)
  | .neg a => env.neg (a.evalWith env)

/-- Height of table `t`. -/
def Trace.height {F : Type} (tr : Trace F) (t : Nat) : Nat := 2 ^ tr.log t

section
variable {F : Type} [Lean.Grind.CommRing F]

/-- The environment of row `r` of table `t` of a trace. -/
def rowEnv (tr : Trace F) (t r : Nat) (pub : List F) : Env F where
  ofNat := fun n => @Nat.cast F Lean.Grind.Semiring.natCast n
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  col := fun c nx => tr.cell t (if nx then (r + 1) % tr.height t else r) c
  pub := fun i => pub.getD i 0
  isFirst := if r = 0 then 1 else 0
  isLast := if r + 1 = tr.height t then 1 else 0
  isTransition := if r + 1 = tr.height t then 0 else 1

/-- `Expr.eval e tr t r pub`: value of `e` on row `r` of table `t`. -/
def Expr.eval (e : Expr) (tr : Trace F) (t r : Nat) (pub : List F) : F :=
  e.evalWith (rowEnv tr t r pub)

end

/-! ## Degrees and well-formedness -/

/-- Formal degree in the trace polynomials; each selector counts as degree 1
(its interpolant has degree `< 2^log`, i.e. it scales like one column). -/
def Expr.degree : Expr → Nat
  | .const _ | .pub _ => 0
  | .col _ _ | .isFirst | .isLast | .isTransition => 1
  | .add a b => max a.degree b.degree
  | .mul a b => a.degree + b.degree
  | .neg a => a.degree

/-- Largest column index read, plus one (`0` if none). -/
def Expr.colBound : Expr → Nat
  | .col c _ => c + 1
  | .add a b | .mul a b => max a.colBound b.colBound
  | .neg a => a.colBound
  | _ => 0

/-- Largest public-input index read, plus one (`0` if none). -/
def Expr.pubBound : Expr → Nat
  | .pub i => i + 1
  | .add a b | .mul a b => max a.pubBound b.pubBound
  | .neg a => a.pubBound
  | _ => 0

/-- Every expression of an interaction. -/
def Interaction.exprs (i : Interaction) : List Expr := i.mult ++ i.msg

/-- Every expression of a table. -/
def Table.exprs (T : Table) : List Expr :=
  T.constraints ++ T.interactions.flatMap Interaction.exprs

/-- The booleanity constraints `b·(b - 1) = 0` of all multiplicity bits.
The protocol adds them to the table's constraints (`Table.allConstraints`). -/
def Table.bitConstraints (T : Table) : List Expr :=
  T.interactions.flatMap fun i => i.mult.map fun b => .mul b (.add b (.neg (.const 1)))

/-- The constraints the protocol actually enforces locally. -/
def Table.allConstraints (T : Table) : List Expr := T.constraints ++ T.bitConstraints

/-- Bounds the protocol relies on (decidable; checked by the verifier):
columns within width, public inputs within `numPub`, buses within
`numBuses`, heights within the field's two-adicity budget (`maxLog ≤ 22`),
at most 25 multiplicity bits, and constraint degree at most `maxDeg`. -/
def Table.wf (A : Air) (maxDeg : Nat) (T : Table) : Bool :=
  T.exprs.all (fun e => decide (e.colBound ≤ T.width) && decide (e.pubBound ≤ A.numPub)) &&
  T.interactions.all (fun i => decide (i.bus < A.numBuses) && decide (i.mult.length ≤ 25)) &&
  T.allConstraints.all (fun e => decide (e.degree ≤ maxDeg)) &&
  decide (1 ≤ T.maxLog) && decide (T.maxLog ≤ 22)

def Air.wf (A : Air) (maxDeg : Nat) : Bool := A.tables.all (Table.wf A maxDeg)

/-! ## The semantic predicate `Holds` -/

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

/-- Multiplicity of interaction `i` on row `r` of table `t`, as a natural:
`Σₖ [bₖ = 1]·2^k`.  (With booleanity, this is exactly `Σₖ bₖ·2^k`.) -/
def Interaction.multNat (i : Interaction) (tr : Trace F) (t r : Nat) (pub : List F) : Nat :=
  go i.mult 0
where
  go : List Expr → Nat → Nat
    | [], _ => 0
    | b :: bs, k => (if b.eval tr t r pub = 1 then 2 ^ k else 0) + go bs (k + 1)

/-- Message of interaction `i` on row `r` of table `t`. -/
def Interaction.msgVal (i : Interaction) (tr : Trace F) (t r : Nat) (pub : List F) : List F :=
  i.msg.map fun e => e.eval tr t r pub

/-- Total multiplicity with which table `t` (with interactions `is`) sends
(`send = true`) or receives message `m` on bus `b`, over all its rows. -/
def tableBusCount (is : List Interaction) (tr : Trace F) (t : Nat) (pub : List F)
    (b : Nat) (send : Bool) (m : List F) : Nat :=
  (List.range (tr.height t)).foldr (fun r acc =>
    is.foldr (fun i acc' =>
      (if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0)
        + acc') acc) 0

/-- Total multiplicity of message `m` on bus `b`, over all tables. -/
def busCount (A : Air) (tr : Trace F) (pub : List F) (b : Nat) (send : Bool) (m : List F) :
    Nat :=
  go A.tables 0
where
  go : List Table → Nat → Nat
    | [], _ => 0
    | T :: Ts, t => tableBusCount T.interactions tr t pub b send m + go Ts (t + 1)

/-- **The AIR semantic predicate** (no challenges).  Table `t` is
`A.tables[t]`; rows are `r < 2^(tr.log t)`. -/
structure Holds (A : Air) (pub : List F) (tr : Trace F) : Prop where
  /-- Heights within `[2, 2^maxLog]` (the protocol's smallest LDE domain
  must hold the final FRI layer, so tables have at least two rows). -/
  logBound : ∀ t (ht : t < A.tables.length), 1 ≤ tr.log t ∧ tr.log t ≤ A.tables[t].maxLog
  /-- Every constraint vanishes on every row. -/
  constr : ∀ t (ht : t < A.tables.length), ∀ r, r < tr.height t →
    ∀ e ∈ A.tables[t].constraints, e.eval tr t r pub = 0
  /-- Every multiplicity bit is boolean on every row. -/
  bits : ∀ t (ht : t < A.tables.length), ∀ r, r < tr.height t →
    ∀ i ∈ A.tables[t].interactions, ∀ b ∈ i.mult,
      b.eval tr t r pub = 0 ∨ b.eval tr t r pub = 1
  /-- Every bus balances, as a multiset of messages with natural multiplicities. -/
  balance : ∀ b m, busCount A tr pub b true m = busCount A tr pub b false m

end

end ZkFormal.Air
