import ZkFormal.Air.Basic
import ZkFormal.Near.Ids

/-!
# ZkFormal.Near.Tables.Dsl — expression builders for the NEAR tables

`c x` / `n x`: column `x` on the current / next row; `k v`: constant;
`sub`, `sum`, `smul`; `eqG g x y = g·(x − y)`; `bool x = x·(x − 1)`;
`send`/`recv` build single-bit interactions.  Kept tiny and structural so
that the evaluation lemmas (`Near.Tables.DslEval`) are one-liners.
-/

namespace ZkFormal.Near.Dsl

open ZkFormal.Air

def c (x : Nat) : Expr := .col x false
def n (x : Nat) : Expr := .col x true
def k (v : Nat) : Expr := .const v
def sub (a b : Expr) : Expr := .add a (.neg b)
def sum : List Expr → Expr
  | [] => .const 0
  | e :: es => .add e (sum es)
def smul (v : Nat) (e : Expr) : Expr := .mul (.const v) e
def mul3 (a b d : Expr) : Expr := .mul (.mul a b) d
def not (x : Expr) : Expr := sub (k 1) x
/-- `g·(x − y)` -/
def eqG (g x y : Expr) : Expr := .mul g (sub x y)
/-- `x·(x − 1)` -/
def bool (x : Expr) : Expr := .mul x (sub x (k 1))
/-- `Σ_{b<len} 2^b · x (off + b)` -/
def bits (x : Nat → Expr) (off len : Nat) : Expr :=
  sum ((List.range len).map fun b => smul (2 ^ b) (x (off + b)))
/-- The SHA message id `kind + 16·idx`. -/
def mid (kind : Nat) (idx : Expr) : Expr := .add (k kind) (smul 16 idx)

/-- Single-bit send / receive. -/
def send (bus : Nat) (gate : Expr) (msg : List Expr) : Interaction :=
  { bus := bus, mult := [gate], msg := msg, send := true }
def recv (bus : Nat) (gate : Expr) (msg : List Expr) : Interaction :=
  { bus := bus, mult := [gate], msg := msg, send := false }

/-- Column allocator: `cols off names` gives consecutive indices. -/
def vec (off len : Nat) (i : Nat) : Nat := off + i

end ZkFormal.Near.Dsl
