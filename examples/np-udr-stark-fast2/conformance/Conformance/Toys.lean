import ZkFormal.Air.Basic

/-!
# Conformance.Toys — the toy AIRs of milestone M1, written in Lean

These mirror `examples/np-udr-stark/source/src/toy.rs` term for term
(`sub a b` is `a + (-b)`), so that `Air.exportJson` of each equals
`npudr export <name>` byte for byte.
-/

namespace Conformance

open ZkFormal.Air

private def sub (a b : Expr) : Expr := .add a (.neg b)
private def first (e : Expr) : Expr := .mul .isFirst e
private def trans (e : Expr) : Expr := .mul .isTransition e
private def cur (c : Nat) : Expr := .col c false
private def nxt (c : Nat) : Expr := .col c true

/-- `pub i + 256·pub(i+1) + 2^16·pub(i+2) + 2^24·pub(i+3)` (left-nested). -/
def pubU32 (i : Nat) : Expr :=
  [1, 2, 3].foldl (fun e k => .add e (.mul (.const (2 ^ (8 * k))) (.pub (i + k)))) (.pub i)

/-- Fibonacci: columns `(a, b)`; `a₀ = pub0`, `b₀ = pub1`, `(a,b)' = (b, a+b)`,
last `b = u32le(pub2..pub5)`. -/
def fibTable (maxLog : Nat) : Table where
  width := 2
  constraints :=
    [ first (sub (cur 0) (.pub 0)),
      first (sub (cur 1) (.pub 1)),
      trans (sub (nxt 0) (cur 1)),
      trans (sub (nxt 1) (.add (cur 0) (cur 1))),
      .mul .isLast (sub (cur 1) (pubU32 2)) ]
  interactions := []
  maxLog := maxLog

def fibAir : Air := { tables := [fibTable 22], numBuses := 0, numPub := 6 }

/-- Cube chain of width `w`: `x'_c = x_c^3 + c`, first row `x_c = c + 2`. -/
def cubeTable (w maxLog : Nat) : Table where
  width := w
  constraints := (List.range w).flatMap fun c =>
    let cube := Expr.mul (cur c) (.mul (cur c) (cur c))
    [ trans (sub (nxt c) (.add cube (.const c))),
      first (sub (cur c) (.const (c + 2))) ]
  interactions := []
  maxLog := maxLog

/-- Mixed heights: fib, cube(3), cube(1). -/
def multiAir : Air :=
  { tables := [fibTable 22, cubeTable 3 22, cubeTable 1 22], numBuses := 0, numPub := 6 }

def toys : List (String × Air) := [("fib", fibAir), ("multi", multiAir)]

end Conformance
