import ZkFormal.Air.Basic

/-!
# M5T1.Dsl — named-column layouts and expression helpers

The same conventions as lane B's `StateM5a.Dsl` (copied, not imported, so this package builds
without lane B's): a table's columns are a `Layout`, a list of `(name, count)` groups;
`Layout.names` is exported next to the AIR so the trace generator addresses columns by name.
-/

namespace M5T1

open ZkFormal.Air

abbrev Layout := List (String × Nat)

def Layout.off : Layout → String → Nat
  | [], _ => 0
  | (n, k) :: r, s => if n == s then 0 else k + Layout.off r s

def Layout.width (L : Layout) : Nat := (L.map (·.2)).sum

def Layout.names (L : Layout) : List String :=
  L.flatMap fun (n, k) => if k == 1 then [n] else (List.range k).map fun j => s!"{n}.{j}"

instance : Add Expr := ⟨.add⟩
instance : Mul Expr := ⟨.mul⟩
instance : Neg Expr := ⟨.neg⟩
instance : Sub Expr := ⟨fun a b => .add a (.neg b)⟩
instance (n : Nat) : OfNat Expr n := ⟨.const n⟩

def K (v : Nat) : Expr := .const v

/-- Sum of a list (`0` for the empty list). -/
def sumE : List Expr → Expr
  | [] => .const 0
  | [a] => a
  | a :: r => .add a (sumE r)

/-- `x · (x − 1)`: booleanity. -/
def bool (x : Expr) : Expr := x * (x - 1)

def snd (bus : Nat) (m : Expr) (msg : List Expr) : Interaction :=
  { bus, mult := [m], msg, send := true }
def rcv (bus : Nat) (m : Expr) (msg : List Expr) : Interaction :=
  { bus, mult := [m], msg, send := false }
def sndBits (bus : Nat) (bits : List Expr) (msg : List Expr) : Interaction :=
  { bus, mult := bits, msg, send := true }
def rcvBits (bus : Nat) (bits : List Expr) (msg : List Expr) : Interaction :=
  { bus, mult := bits, msg, send := false }

/-- A table-local column accessor. -/
structure Cols where
  L : Layout

def Cols.c (T : Cols) (s : String) (j : Nat := 0) : Expr := .col (T.L.off s + j) false
def Cols.n (T : Cols) (s : String) (j : Nat := 0) : Expr := .col (T.L.off s + j) true

/-- Little-endian bytes of a natural (`len` bytes). -/
def leBytes (v len : Nat) : List Nat := (List.range len).map fun k => v / 256 ^ k % 256

/-- `Σ_k 256^k · b k` for `k < n` (the little-endian value of `n` byte expressions). -/
def leVal (b : Nat → Expr) (n : Nat) : Expr := sumE ((List.range n).map fun k => K (256 ^ k) * b k)

end M5T1
