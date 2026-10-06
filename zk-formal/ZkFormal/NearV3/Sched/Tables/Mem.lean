import ZkFormal.Chacha.Rng.Table
import ZkFormal.NearV3.Sched.Ids

/-!
# ZkFormal.NearV3.Sched.Tables.Mem — `smmV3`: scheduler memory (address-sorted segments)

One row per memory access. The rows of an address form one **segment**: an `INIT` row
(`fst`), then its `READ`/`GRANT` ops in strictly increasing time `t` (comparator), the last row
(`lst`) sends the final value on `SFIN`. Values are chained locally (`vin` of a row = `v` of the
previous row of the segment), so each op reads the latest earlier write (`mem_chain`).
Address kinds (`addrOf τ kind idx`): link (allowance `v`, granted accumulator `w`, allowed flag
`al`) or a sender / receiver budget (`v`). Every access is a received `SOP` message
`(addr, t, op, vin, v, inc, ok, c)`:

* `INIT` (`op = 0`, `t = 0`): `vin = al`, `inc = w` (initial granted), `ok = c = 0`;
* `READ` (`op = 1`): `v = vin`;
* `GRANT` (`op = 2`): the comparator gives `sf = [inc ≤ vin]`; the condition is `c = al` (link)
  or `c = sf` (budget); `ok ⇒ c`; `v = vin − ok·(sf ? inc : vin)` (`saturating_sub` for links;
  budgets need `sf`); links add `ok·inc` to `w`.

| col | name | col | name |
|---|---|---|---|
| 0 | `act` | 9 | `v` |
| 1 | `fst` | 10 | `wp` (granted before) |
| 2 | `lst` | 11 | `w` |
| 3 | `isRd` | 12 | `al` |
| 4 | `isGr` | 13 | `isL` (link address) |
| 5 | `addr` | 14 | `inc` |
| 6 | `t` | 15 | `ok` |
| 7 | `tp` (previous `t`) | 16 | `c` |
| 8 | `vin` | 17 | `sf` |
-/

namespace ZkFormal.NearV3.Sched.Mem

open ZkFormal.Air ZkFormal.Chacha.Table.E
open ZkFormal.Chacha.Table (boolC)

def act : Nat := 0
def fst : Nat := 1
def lst : Nat := 2
def isRd : Nat := 3
def isGr : Nat := 4
def addr : Nat := 5
def t : Nat := 6
def tp : Nat := 7
def vin : Nat := 8
def v : Nat := 9
def wp : Nat := 10
def w : Nat := 11
def al : Nat := 12
def isL : Nat := 13
def inc : Nat := 14
def ok : Nat := 15
def cc : Nat := 16
def sf : Nat := 17
def width : Nat := 18

def boolCols : List Nat := [act, fst, lst, isRd, isGr, al, isL, ok, cc, sf]

/-- Continuing segment (`act ∧ ¬lst`; `lst ⇒ act`). -/
def gE : Expr := sub (c act) (c lst)
def mul3 (a b d : Expr) : Expr := .mul (.mul a b) d
def notE (x : Expr) : Expr := sub (k 1) x

/-- Carried from a row to the next row of its segment. -/
def carried : List (Nat × Nat) := [(addr, addr), (v, vin), (t, tp), (w, wp), (al, al), (isL, isL)]

def constraints : List Expr :=
  boolCols.map boolC ++
  [ sub (c act) (.add (c fst) (.add (c isRd) (c isGr))),
    .mul (c lst) (notE (c act)),
    .mul .isLast (c act),
    .mul .isFirst (sub (c act) (c fst)),
    -- segment continuity
    .mul gE (notE (n act)),
    .mul gE (n fst) ] ++
  carried.map (fun (a, b) => .mul gE (sub (n b) (c a))) ++
  [ mul3 (c lst) (n act) (notE (n fst)),
    mul3 .isTransition (notE (c act)) (n act),
    -- INIT rows
    .mul (c fst) (c t), .mul (c fst) (sub (c vin) (c al)), .mul (c fst) (sub (c inc) (c w)),
    .mul (c fst) (c ok), .mul (c fst) (c cc), .mul (c fst) (c sf), .mul (c fst) (sub (c wp) (c w)),
    -- READ rows
    .mul (c isRd) (sub (c v) (c vin)), .mul (c isRd) (sub (c w) (c wp)), .mul (c isRd) (c inc),
    .mul (c isRd) (c ok), .mul (c isRd) (c cc), .mul (c isRd) (c sf),
    -- GRANT rows
    .mul (c isGr) (sub (c cc) (.add (.mul (c isL) (c al)) (.mul (notE (c isL)) (c sf)))),
    .mul (c isGr) (sub (c v) (sub (c vin)
      (.mul (c ok) (.add (.mul (c sf) (c inc)) (.mul (notE (c sf)) (c vin)))))),
    mul3 (c isGr) (c ok) (notE (c cc)),
    .mul (c isGr) (sub (c w) (.add (c wp) (mul3 (c isL) (c ok) (c inc)))) ]

def opE : Expr := .add (c isRd) (smul 2 (c isGr))

def interactions : List Interaction :=
  [ { bus := B_SOP, mult := [c act], send := false,
      msg := [c addr, c t, opE, c vin, c v, c inc, c ok, c cc] },
    { bus := B_SFIN, mult := [c lst], send := true, msg := [c addr, c v, c w] },
    { bus := B_SCMP, mult := [.add (c isRd) (c isGr)], send := true, msg := [c t, .add (c tp) (k 1), k 1] },
    { bus := B_SCMP, mult := [c isGr], send := true, msg := [c vin, c inc, c sf] } ]

def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.Sched.Mem
