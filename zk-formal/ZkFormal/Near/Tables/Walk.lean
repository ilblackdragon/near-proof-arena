import ZkFormal.Near.Tables.Dsl

/-!
# ZkFormal.Near.Tables.Walk — account-key walks (NEAR-AIR.md §3.2)

One segment per receipt `r`: the walk of its account key
`nibbles (0x00 ‖ receiver) ++ [END]` through the trie edges the `node` table
provides.  States are `(node, nibbles of its key consumed)`.

* row 0 of a walk (`ws`): the `START` step `(0,0) → (res root, 0)`; it reads no
  key symbol;
* every other row consumes symbol `t` of the key from `KEYNIB (r, t, sym, last)`
  (sent by `rcpt`) along an edge `(N, I) –sym→ (N2, I2)`;
* the step consuming `END` (`last = 1`) is the walk's last row (`we`) and sends
  `FINAL (r, N2)`: `N2` is the touched slot.

Edges are consumed through the chained `EDGE` bus: receive `(e, u)`, send
`(e, u + 1)`.
-/

namespace ZkFormal.Near.WalkTab

open ZkFormal.Air ZkFormal.Near.Dsl

def act : Nat := 0
def ws : Nat := 1
def we : Nat := 2
def r : Nat := 3
def t : Nat := 4
def sym : Nat := 5
def nN : Nat := 6
def nI : Nat := 7
def nN2 : Nat := 8
def nI2 : Nat := 9
def u : Nat := 10
/-- gate of the key-symbol receive: `act − ws` -/
def gK : Nat := 11
def width : Nat := 12

def constraints : List Expr :=
  [act, ws, we, gK].map (fun x => bool (c x)) ++
  [ sub (c gK) (sub (c act) (c ws)),
    .mul (c ws) (not (c act)), .mul (c we) (not (c act)),
    .mul (c ws) (c we),
    -- a walk starts at (0,0) with the START step and symbol index 0
    .mul (c ws) (c nN), .mul (c ws) (c nI), .mul (c ws) (sub (c sym) (k SYM_START)),
    .mul (c ws) (c t),
    .mul .isFirst (not (c ws)),
    .mul .isLast (.mul (c act) (not (c we))),
    -- inside a walk
    mul3 (c act) (not (c we)) (not (n act)),
    mul3 (c act) (not (c we)) (n ws),
    mul3 (c act) (not (c we)) (sub (n r) (c r)),
    mul3 (c act) (not (c we)) (sub (n nN) (c nN2)),
    mul3 (c act) (not (c we)) (sub (n nI) (c nI2)),
    mul3 (c act) (not (c we)) (sub (n t) (.add (c t) (c gK))),
    -- after a walk: another walk or padding
    mul3 (c we) (n act) (not (n ws)),
    mul3 .isTransition (not (c act)) (n act) ]

def edge (uu : Expr) : List Expr := [c nN, c nI, c sym, c nN2, c nI2, uu]

def interactions : List Interaction :=
  [ recv B_KEYNIB (c gK) [c r, c t, c sym, c we],
    recv B_EDGE (c act) (edge (c u)),
    send B_EDGE (c act) (edge (.add (c u) (k 1))),
    send B_FINAL (c we) [c r, c nN2] ]

/-- `≤ 256` walks of `≤ 1 + 2·65 + 1` rows. -/
def maxLog : Nat := 16

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.Near.WalkTab
