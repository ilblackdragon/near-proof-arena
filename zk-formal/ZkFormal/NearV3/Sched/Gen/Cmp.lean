import ZkFormal.NearV3.Sched.Tables.Cmp
import ZkFormal.NearV3.Sched.Gen.Run

/-!
# ZkFormal.NearV3.Sched.Gen.Cmp — honest trace of the comparator `scpV3`

One row per comparison `(x, y, b = [y ≤ x])` (`Run.cmps`, the messages the memory and process
tables send on `SCMP`): `act = 1`, bits of `d = b·(x − y) + (1 − b)·(y − x − 1)`. Padding rows:
`x = y = 0, b = 1, d = 0`.
-/

namespace ZkFormal.NearV3.Sched.Gen.Cmp

open ZkFormal.NearV3.Sched.Cmp

def row (x y b : Nat) : Array Nat := Id.run do
  let d := if b = 1 then x - y else y - x - 1
  let mut a := zrow width
  a := a.set! colAct 1 |>.set! colX x |>.set! colY y |>.set! colB b
  for i in List.range nbits do a := a.set! (colD i) (bit d i)
  return a

def padRow : Array Nat := (zrow width).set! colB 1

def rows (cmps : List (Nat × Nat × Nat)) : Array (Array Nat) :=
  cmps.toArray.map fun (x, y, b) => row x y b

def trace (cmps : List (Nat × Nat × Nat)) : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
  mkTrace (rows cmps) 0 fun _ => padRow

/-- Messages received on `SCMP` (multiplicity one each). -/
def expected (cmps : List (Nat × Nat × Nat)) : List (List Nat) := cmps.map fun (x, y, b) => [x, y, b]

end ZkFormal.NearV3.Sched.Gen.Cmp
