import ZkFormal.Air.Basic
import ZkFormal.Algebra.Fp

/-!
# ZkFormal.NearV3.Sched.Gen.Common — helpers of the scheduler trace generators (lane `v3-sched`)

Rows are `Array Nat` with every entry `< p` (a field element given by its canonical
representative; `fneg x = p − x`, `finv x` = the inverse of `x mod p`, `0 ↦ 0`). A table trace
is the row list padded to a power-of-two height with a padding-row function.
-/

namespace ZkFormal.NearV3.Sched.Gen

open ZkFormal.Air ZkFormal.Algebra

/-- `−x mod p` for `x < p`. -/
def fneg (x : Nat) : Nat := (P - x % P) % P

/-- Inverse of `x mod p` (`0 ↦ 0`). -/
def finv (x : Nat) : Nat := if x % P = 0 then 0 else ((Fp.ofNat x)⁻¹ : Fp).toNat

/-- `(a − b) mod p`. -/
def fsub (a b : Nat) : Nat := (a % P + P - b % P) % P

def bit (x b : Nat) : Nat := x / 2 ^ b % 2

def b2n (b : Bool) : Nat := if b then 1 else 0

/-- Smallest `log` with `m ≤ 2^log` (structural, fuel `m`, so that heights can be reasoned
about: `Complete/Trace.lean`, `clog2_ge` / `clog2_le`). -/
def clog2 (m : Nat) : Nat := go m 0 where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | fuel + 1, acc => if m ≤ 2 ^ acc then acc else go fuel (acc + 1)

/-- A row builder: `width` zeros, then `set` writes. -/
def zrow (width : Nat) : Array Nat := Array.replicate width 0

/-- Trace of one table (table index ignored): rows, then padding rows `pad r` (`r` = global
row index) up to `2^log`, `log = max 1 (clog2 (rows + extra))` (`extra = 1` when the table
needs a final padding row). -/
def mkTrace (rows : Array (Array Nat)) (extra : Nat) (pad : Nat → Array Nat) : Trace Fp :=
  let log := max 1 (clog2 (rows.size + extra))
  let all : Array (Array Fp) := (List.range (2 ^ log)).toArray.map fun r =>
    (if h : r < rows.size then rows[r] else pad r).map Fp.ofNat
  ⟨fun _ => log, fun _ r c => (all.getD r #[]).getD c 0⟩

/-- An expected bus message `(bus, send, msg)` from outside the tables (public data, other
tables), multiplicity one. -/
abbrev Msg := Nat × Bool × List Nat

end ZkFormal.NearV3.Sched.Gen
