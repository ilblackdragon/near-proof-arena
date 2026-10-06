/-!
# NEAR WASM (D3α): integer numerics (WebAssembly 2.0 §4.3.2)

Width-generic definitions over `Nat` representatives `0 ≤ a < 2^w` (w ∈ {32, 64}). `none` means
trap. nearcore maps wasmtime's `IntegerDivisionByZero` and `IntegerOverflow` both to
`WasmTrap::IllegalArithmetic` (`wasmtime_runner/mod.rs:391-392`).
-/
namespace NearSpecV3.Wasm.Num

def signed (w a : Nat) : Int := if a ≥ 2 ^ (w - 1) then (a : Int) - 2 ^ w else a
def wrap (w : Nat) (i : Int) : Nat := (i % (2 ^ w : Int)).toNat
def bit (a i : Nat) : Bool := (a / 2 ^ i) % 2 = 1
def b2 (b : Bool) : Nat := if b then 1 else 0

def clz (w a : Nat) : Nat := Id.run do
  for i in [0:w] do
    if bit a (w - 1 - i) then return i
  return w

def ctz (w a : Nat) : Nat := Id.run do
  for i in [0:w] do
    if bit a i then return i
  return w

def popcnt (w a : Nat) : Nat := Id.run do
  let mut n := 0
  for i in [0:w] do
    if bit a i then n := n + 1
  return n

def shl (w a b : Nat) : Nat := (a * 2 ^ (b % w)) % 2 ^ w
def shrU (w a b : Nat) : Nat := a / 2 ^ (b % w)
/-- arithmetic shift: `Int./` by a positive power of two is floor division -/
def shrS (w a b : Nat) : Nat := wrap w (signed w a / (2 ^ (b % w) : Int))
def rotl (w a b : Nat) : Nat := let k := b % w; (a * 2 ^ k) % 2 ^ w + a / 2 ^ (w - k)
def rotr (w a b : Nat) : Nat := rotl w a ((w - b % w) % w)

def divS (w a b : Nat) : Option Nat :=
  if b = 0 then none
  else if signed w a = -(2 ^ (w - 1) : Int) ∧ signed w b = -1 then none
  else some (wrap w (Int.tdiv (signed w a) (signed w b)))
def remS (w a b : Nat) : Option Nat :=
  if b = 0 then none else some (wrap w (Int.tmod (signed w a) (signed w b)))

/-- sign-extend the low `k` bits to width `w` -/
def extendS (w k a : Nat) : Nat := wrap w (signed k (a % 2 ^ k))

def unop (w op a : Nat) : Nat :=
  match op with
  | 0 => clz w a
  | 1 => ctz w a
  | _ => popcnt w a

/-- binary op by index `k` = opcode − base (`add`=0 … `rotr`=14) -/
def binop (w k a b : Nat) : Option Nat :=
  match k with
  | 0 => some ((a + b) % 2 ^ w)
  | 1 => some ((a + 2 ^ w - b) % 2 ^ w)
  | 2 => some ((a * b) % 2 ^ w)
  | 3 => divS w a b
  | 4 => if b = 0 then none else some (a / b)
  | 5 => remS w a b
  | 6 => if b = 0 then none else some (a % b)
  | 7 => some (a &&& b)
  | 8 => some (a ||| b)
  | 9 => some (a ^^^ b)
  | 10 => some (shl w a b)
  | 11 => some (shrS w a b)
  | 12 => some (shrU w a b)
  | 13 => some (rotl w a b)
  | _ => some (rotr w a b)

/-- relational op by index (`eq`=0 … `ge_u`=9) -/
def relop (w k a b : Nat) : Bool :=
  match k with
  | 0 => a = b
  | 1 => a ≠ b
  | 2 => signed w a < signed w b
  | 3 => a < b
  | 4 => signed w a > signed w b
  | 5 => a > b
  | 6 => signed w a ≤ signed w b
  | 7 => a ≤ b
  | 8 => signed w a ≥ signed w b
  | _ => a ≥ b

end NearSpecV3.Wasm.Num
