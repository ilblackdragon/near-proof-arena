import ZkFormal.Chacha.Rng.Table
import ZkFormal.NearV3.Sched.Ids

/-!
# ZkFormal.NearV3.Sched.Tables.Dist — `sdsV3`: budgets and `distribute_remaining_bandwidth`

Per instance τ: **shard rows** for the senders (`side = 0`) then the receivers (`side = 1`), each
side in *sorted* order `pos = 0 … n−1` (`Spec/Dist.sortByKey_eq_of_sorted`: the key
`avg·64 + shard` strictly increases, comparator); then the **grid**: for each sender position
`i` a **header** row and the **cells** `j = 0 … n−1` (`Spec/Dist.gridGrants_get`).

A shard row receives the public `(τ, side, shard, links, B₀, n)` (`B₀` = budget after the base
grants, claim-only), INITs the budget's memory segment, receives its final value `left`
(after the process phase), computes `avg = left / links` (`0` if `links = 0`; remainder by
bits), and sends its endpoint into the grid on `SDLX`: senders as `(τ, i, 255, s, links, left)`
(received by header `i`), receivers as `(τ, 0, j, r, links, left)` (received by cell `(0, j)`).
A cell `(i, j)` receives the receiver endpoint `(RN, RL)`, keeps the sender endpoint `(SN, SL)`
along the row, reads the public `allowed` of link `l = s·n + r`, and on an allowed link grants
`gb = min(⌊SL/SN⌋, ⌊RL/RN⌋)`; it passes `(RN − al, RL − gb)` to cell `(i+1, j)` and sends
`(τ, l, al, gb)` to the codec.

Multiplexed columns: shard rows keep their shard / links / left / avg / remainder in the cell's
receiver columns `r, N2, L2, q2, r2`.
-/

namespace ZkFormal.NearV3.Sched.Dist

open ZkFormal.Air ZkFormal.Chacha.Table.E
open ZkFormal.Chacha.Table (boolC)

def act : Nat := 0
def kSh : Nat := 1
def kGH : Nat := 2
def kC : Nat := 3
def tau : Nat := 4
def nn : Nat := 5
def side : Nat := 6
def a : Nat := 7
def b : Nat := 8
def s : Nat := 9
def r : Nat := 10
def N1 : Nat := 11
def L1 : Nat := 12
def N2 : Nat := 13
def L2 : Nat := 14
def by0 : Nat := 15
def by1 : Nat := 16
def by2 : Nat := 17
def q1 : Nat := 18
def r1 : Nat := 19
def bt1 (i : Nat) : Nat := 20 + i
def q2 : Nat := 26
def r2 : Nat := 27
def bt2 (i : Nat) : Nat := 28 + i
def icnt : Nat := 34
def zc : Nat := 35
def kp : Nat := 36
def da : Nat := 37
def db : Nat := 38
def llo : Nat := 39
def lhi : Nat := 40
def al : Nat := 41
def gb : Nat := 42
def ig1 : Nat := 43
def e1 : Nat := 44
def ig2 : Nat := 45
def e2 : Nat := 46
def cx : Nat := 47
def cy : Nat := 48
def cb : Nat := 49
def cg : Nat := 50
def dlsg : Nat := 51
def dlrg : Nat := 52
def sL : Nat := 53
/-- End of an instance's grid (`kC ∧ e1 ∧ e2`). -/
def eI : Nat := 54
/-- Range checks: bits of `q1, q2` (23 each) and `r1, r2` (6 each). -/
def qb1 (i : Nat) : Nat := 55 + i
def qb2 (i : Nat) : Nat := 78 + i
def rb1 (i : Nat) : Nat := 101 + i
def rb2 (i : Nat) : Nat := 107 + i
def width : Nat := 113

def mul3 (x y w : Expr) : Expr := .mul (.mul x y) w
def notE (e : Expr) : Expr := sub (k 1) e

def boolCols : List Nat :=
  [act, kSh, kGH, kC, side, zc, al, e1, e2, cb, cg, dlsg, dlrg, eI] ++
  (List.range 6).map bt1 ++ (List.range 6).map bt2 ++
  (List.range 23).map qb1 ++ (List.range 23).map qb2 ++ (List.range 6).map rb1 ++ (List.range 6).map rb2

def bits1E : Expr := ZkFormal.Chacha.Rng.Table.num bt1 6
def bits2E : Expr := ZkFormal.Chacha.Rng.Table.num bt2 6
def b0E : Expr := .add (c by0) (.add (smul 256 (c by1)) (smul 65536 (c by2)))
def addrE : Expr := .add (smul 16384 (c tau)) (.add (smul 4096 (.add (c side) (k 1))) (c r))
def linkE : Expr := .add (c llo) (smul 256 (c lhi))
/-- Gadget operand: shard rows `pos`, cells `j`. -/
def x1E : Expr := .add (.mul (c kSh) (c a)) (.mul (c kC) (c b))
/-- Instance constants. -/
def instCols : List Nat := [tau, nn]

def cKind : List Expr :=
  boolCols.map boolC ++
  [ sub (c act) (.add (c kSh) (.add (c kGH) (c kC))),
    .mul .isLast (c act),
    mul3 .isTransition (notE (c act)) (n act),
    .mul .isFirst (.mul (c act) (notE (c kSh))),
    .mul .isFirst (c side), .mul .isFirst (c a), .mul .isFirst (c kp),
    -- e1 = [x1 = n − 1] on shard rows and cells; e2 = [a = n − 1] on cells
    .mul (.add (c kSh) (c kC)) (sub (c e1) (notE (.mul (sub x1E (sub (c nn) (k 1))) (c ig1)))),
    .mul (.add (c kSh) (c kC)) (.mul (sub x1E (sub (c nn) (k 1))) (c e1)),
    .mul (c kC) (sub (c e2) (notE (.mul (sub (c a) (sub (c nn) (k 1))) (c ig2)))),
    .mul (c kC) (.mul (sub (c a) (sub (c nn) (k 1))) (c e2)) ]

def cShard : List Expr :=
  [ -- avg / remainder (links = N2, left = L2, avg = q2, rem = r2)
    .mul (c kSh) (sub (c zc) (notE (.mul (c N2) (c icnt)))),
    mul3 (c kSh) (c N2) (c zc),
    mul3 (c kSh) (notE (c zc)) (sub (c L2) (.add (.mul (c q2) (c N2)) (c r2))),
    mul3 (c kSh) (notE (c zc)) (sub (sub (sub (c N2) (k 1)) (c r2)) bits2E),
    mul3 (c kSh) (c zc) (c q2),
    -- order: key = avg·64 + shard ≥ kp; next kp = key + 1; kp = 0 at a side start
    .mul (c kSh) (sub (c cx) (.add (smul 64 (c q2)) (c r))),
    .mul (c kSh) (sub (c cy) (c kp)),
    .mul (c kSh) (sub (c cb) (k 1)),
    mul3 (c kSh) (notE (c e1)) (sub (n kp) (.add (c cx) (k 1))),
    mul3 (c kSh) (c e1) (n kp),
    -- grid endpoint message
    .mul (c kSh) (sub (c da) (.mul (notE (c side)) (c a))),
    .mul (c kSh) (sub (c db) (.add (.mul (c side) (c a)) (smul 255 (notE (c side))))),
    .mul (c kSh) (sub (c sL) (c L2)),
    .mul (c kSh) (c al),
    -- transitions
    mul3 (c kSh) (notE (c e1)) (notE (n kSh)),
    mul3 (c kSh) (notE (c e1)) (sub (n side) (c side)),
    mul3 (c kSh) (notE (c e1)) (sub (n a) (.add (c a) (k 1))),
    mul3 (c kSh) (c e1) (.mul (notE (c side)) (notE (n kSh))),
    mul3 (c kSh) (c e1) (.mul (notE (c side)) (sub (n side) (k 1))),
    mul3 (c kSh) (c e1) (.mul (notE (c side)) (n a)),
    mul3 (c kSh) (c e1) (.mul (c side) (notE (n kGH))),
    mul3 (c kSh) (c e1) (.mul (c side) (n a)) ] ++
  instCols.map (fun x => .mul (c kSh) (sub (n x) (c x)))

def cGrid : List Expr :=
  [ -- header: receives the sender endpoint into (r, N2, L2), passes it to cell (a, 0)
    .mul (c kGH) (sub (c b) (k 255)),
    .mul (c kGH) (notE (n kC)),
    .mul (c kGH) (n b),
    .mul (c kGH) (sub (n a) (c a)),
    .mul (c kGH) (sub (n s) (c r)),
    .mul (c kGH) (sub (n N1) (c N2)),
    .mul (c kGH) (sub (n L1) (c L2)) ] ++
  instCols.map (fun x => .mul (c kGH) (sub (n x) (c x))) ++
  [ -- cell: link, allowed, divisions, grant
    .mul (c kC) (sub linkE (.add (.mul (c s) (c nn)) (c r))),
    .mul (c al) (notE (c kC)),
    .mul (c al) (sub (c L1) (.add (.mul (c q1) (c N1)) (c r1))),
    .mul (c al) (sub (sub (sub (c N1) (k 1)) (c r1)) bits1E),
    .mul (c al) (sub (c L2) (.add (.mul (c q2) (c N2)) (c r2))),
    .mul (c al) (sub (sub (sub (c N2) (k 1)) (c r2)) bits2E),
    .mul (c kC) (sub (c cx) (c q1)),
    .mul (c kC) (sub (c cy) (c q2)),
    .mul (c al) (sub (c gb) (.add (.mul (c cb) (c q2)) (.mul (notE (c cb)) (c q1)))),
    .mul (c kC) (.mul (notE (c al)) (c gb)),
    sub (c cg) (.add (c kSh) (.mul (c kC) (c al))),
    -- receiver endpoint down the column
    .mul (c kC) (sub (c da) (.add (c a) (k 1))),
    .mul (c kC) (sub (c db) (c b)),
    .mul (c kC) (sub (c sL) (sub (c L2) (c gb))),
    sub (c dlsg) (.add (c kSh) (.mul (c kC) (notE (c e2)))),
    sub (c dlrg) (.add (c kGH) (c kC)),
    -- along the row
    mul3 (c kC) (notE (c e1)) (notE (n kC)),
    mul3 (c kC) (notE (c e1)) (sub (n a) (c a)),
    mul3 (c kC) (notE (c e1)) (sub (n b) (.add (c b) (k 1))),
    mul3 (c kC) (notE (c e1)) (sub (n s) (c s)),
    mul3 (c kC) (notE (c e1)) (sub (n N1) (sub (c N1) (c al))),
    mul3 (c kC) (notE (c e1)) (sub (n L1) (sub (c L1) (c gb))) ] ++
  instCols.map (fun x => mul3 (c kC) (notE (c e1)) (sub (n x) (c x))) ++
  [ -- row end: next header (a + 1) or the end of the instance
    mul3 (c kC) (c e1) (.mul (notE (c e2)) (notE (n kGH))),
    mul3 (c kC) (c e1) (.mul (notE (c e2)) (sub (n a) (.add (c a) (k 1)))) ] ++
  instCols.map (fun x => mul3 (c kC) (c e1) (.mul (notE (c e2)) (sub (n x) (c x)))) ++
  [ -- a new instance starts with sender shard row 0 (kp = 0)
    sub (c eI) (mul3 (c kC) (c e1) (c e2)),
    mul3 (c eI) (n act) (notE (n kSh)),
    mul3 (c eI) (n act) (n side),
    mul3 (c eI) (n act) (n a),
    .mul (c eI) (n kp) ]

/-- Quotients `< 2^23` and remainders `< 64` on every row, so every division is an integer
division (`q·N + r < 2^30 < P`). -/
def cRange : List Expr :=
  [ sub (c q1) (ZkFormal.Chacha.Rng.Table.num qb1 23), sub (c q2) (ZkFormal.Chacha.Rng.Table.num qb2 23),
    sub (c r1) (ZkFormal.Chacha.Rng.Table.num rb1 6), sub (c r2) (ZkFormal.Chacha.Rng.Table.num rb2 6) ]

def constraints : List Expr := cKind ++ cShard ++ cGrid ++ cRange

def interactions : List Interaction :=
  [ { bus := B_SSHD, mult := [c kSh], send := false,
      msg := [c tau, c side, c r, c N2, c by0, c by1, c by2, c nn] },
    { bus := B_SOP, mult := [c kSh], send := true,
      msg := [addrE, k 0, k OP_INIT, k 0, b0E, k 0, k 0, k 0] },
    { bus := B_SFIN, mult := [c kSh], send := false, msg := [addrE, c L2, k 0] },
    { bus := B_SCMP, mult := [c cg], send := true, msg := [c cx, c cy, c cb] },
    { bus := B_SDLX, mult := [c dlsg], send := true,
      msg := [c tau, c da, c db, c r, sub (c N2) (c al), c sL] },
    { bus := B_SDLX, mult := [c dlrg], send := false,
      msg := [c tau, c a, c b, c r, c N2, c L2] },
    { bus := B_SLINK, mult := [c kC], send := false, msg := [c tau, c llo, c lhi, c al] },
    { bus := B_SDG, mult := [c kC], send := true, msg := [c tau, linkE, c al, c gb] } ]

def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.Sched.Dist
