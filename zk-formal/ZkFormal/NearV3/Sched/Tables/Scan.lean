import ZkFormal.Chacha.Rng.Table
import ZkFormal.NearV3.Sched.Ids

/-!
# ZkFormal.NearV3.Sched.Tables.Scan — `sscV3`: request bitmaps → increases (`convertRequest`)

Per instance τ with requests: a **param row** (public `SPAR (τ, 1, n, base₀..₂, D₀..₂, 0, 0)`,
`D = max_single_grant − base`), then each converted request `cid = 0, 1, …` (public
`SRAW (τ, cid_lo, cid_hi, s, r, bm₀ … bm₄)`, only requests with a set bit are published) as
**20 rows**, row `(y, u)` holding bitmap bits `2(4y+u)` and `2(4y+u)+1`. The bytes sit in a
register `q₀ … q₄` that is consumed two bits per row (`q₀ = b₀ + 2b₁ + 4·q₀'`, exhausted at the
byte end, then rotated), so the bits are exactly the bitmap. For a set bit at position `c`:
`v[c] = base + ⌊D(c+1)/40⌋` (remainders `< 40` by bits), the increase is `v[c] − cur`
(`cur` = value of the previous set bit, `base` first, `Spec/Conv`), sent as
`INC (τ, cid·64 + j, inc, m − j − 1, s, r, link)` with multiplicity `used ≤ bit`
(`m` = number of set bits, checked at the request end). At the request end the initial push
`(τ, key, [key = 0], cid, cid·64)` is sent with a memory READ of the link at time `cid + 1`.

Multiplexed columns: the param row keeps `base₀..₂` in `q₀..q₂` and `D₀..₂` in `q₃, q₄, clo`.
-/

namespace ZkFormal.NearV3.Sched.Scan

open ZkFormal.Air ZkFormal.Chacha.Table.E
open ZkFormal.Chacha.Table (boolC)

def act : Nat := 0
def kP : Nat := 1
def kS : Nat := 2
def fQ : Nat := 3
def tau : Nat := 4
def nn : Nat := 5
def base : Nat := 6
def dd : Nat := 7
def cid : Nat := 8
def clo : Nat := 9
def chi : Nat := 10
def s : Nat := 11
def r : Nat := 12
def link : Nat := 13
def q (i : Nat) : Nat := 14 + i
def b0 : Nat := 19
def b1 : Nat := 20
def u0 : Nat := 21
def u1 : Nat := 22
def y : Nat := 23
def iy : Nat := 24
def e4 : Nat := 25
def re : Nat := 26
def Q0 : Nat := 27
def Q1 : Nat := 28
def rb0 (i : Nat) : Nat := 29 + i
def rb1 (i : Nat) : Nat := 35 + i
def cur : Nat := 41
def cm : Nat := 42
def j : Nat := 43
def m : Nat := 44
def key : Nat := 45
def ikey : Nat := 46
def zk0 : Nat := 47
def us0 : Nat := 48
def us1 : Nat := 49
def width : Nat := 50

def mul3 (a b d : Expr) : Expr := .mul (.mul a b) d
def notE (e : Expr) : Expr := sub (k 1) e

def boolCols : List Nat :=
  [act, kP, kS, fQ, b0, b1, u0, u1, e4, re, zk0, us0, us1] ++
  (List.range 6).map rb0 ++ (List.range 6).map rb1

/-- Byte end (`u = 3`). -/
def be : Expr := .mul (c u0) (c u1)
def uE : Expr := .add (c u0) (smul 2 (c u1))
/-- Bit position of `b₀`. -/
def posE : Expr := .add (smul 8 (c y)) (smul 2 uE)
def r0E : Expr := ZkFormal.Chacha.Rng.Table.num rb0 6
def r1E : Expr := ZkFormal.Chacha.Rng.Table.num rb1 6
def val0 : Expr := .add (c base) (c Q0)
def val1 : Expr := .add (c base) (c Q1)
/-- Continuing request row. -/
def gC : Expr := sub (c kS) (c re)

/-- Request constants. -/
def reqCols : List Nat := [tau, nn, base, dd, cid, s, r, link, m, key]
/-- Instance constants (kept from one request to the next and from the param row). -/
def instCols : List Nat := [tau, nn, base, dd]

def constraints : List Expr :=
  boolCols.map boolC ++
  [ sub (c act) (.add (c kP) (c kS)),
    .mul (c fQ) (notE (c kS)),
    .mul (c re) (notE (c kS)),
    .mul (c us0) (notE (c b0)), .mul (c us1) (notE (c b1)),
    .mul (c us0) (notE (c kS)), .mul (c us1) (notE (c kS)),
    .mul .isLast (c act),
    mul3 .isTransition (notE (c act)) (n act),
    .mul .isFirst (.mul (c act) (notE (c kP))),
    -- param row
    .mul (c kP) (sub (c base) (.add (c (q 0)) (.add (smul 256 (c (q 1))) (smul 65536 (c (q 2)))))),
    .mul (c kP) (sub (c dd) (.add (c (q 3)) (.add (smul 256 (c (q 4))) (smul 65536 (c clo))))),
    .mul (c kP) (notE (n fQ)),
    .mul (c kP) (n cid) ] ++
  instCols.map (fun x => .mul (c kP) (sub (n x) (c x))) ++
  [ -- first row of a request
    .mul (c fQ) (c u0), .mul (c fQ) (c u1), .mul (c fQ) (c y), .mul (c fQ) (c j),
    .mul (c fQ) (sub (c cur) (c base)),
    .mul (c fQ) (sub (c cid) (.add (c clo) (smul 256 (c chi)))),
    .mul (c fQ) (sub (c link) (.add (.mul (c s) (c nn)) (c r))),
    -- inside a request
    .mul gC (notE (n kS)), .mul gC (n fQ),
    .mul gC (sub (n cur) (.add (.mul (c b1) val1) (.mul (notE (c b1)) (c cm)))),
    .mul gC (sub (n j) (.add (c j) (.add (c b0) (c b1)))),
    .mul gC (sub (.add (n u0) (smul 2 (n u1))) (sub (.add uE (k 1)) (smul 4 be))),
    .mul gC (sub (n y) (.add (c y) be)),
    -- the byte register
    mul3 (c kS) be (sub (c (q 0)) (.add (c b0) (smul 2 (c b1)))),
    mul3 gC (notE be) (sub (c (q 0)) (.add (c b0) (.add (smul 2 (c b1)) (smul 4 (n (q 0)))))) ] ++
  (List.range 4).map (fun i => mul3 gC be (sub (n (q i)) (c (q (i + 1))))) ++
  (List.range 4).map (fun i => mul3 gC (notE be) (sub (n (q (i + 1))) (c (q (i + 1))))) ++
  reqCols.map (fun x => .mul gC (sub (n x) (c x))) ++
  [ -- request end: e4 = [y = 4], re = e4·be, m = j + b₀ + b₁
    .mul (c kS) (sub (c e4) (notE (.mul (sub (c y) (k 4)) (c iy)))),
    .mul (sub (c y) (k 4)) (c e4),
    sub (c re) (mul3 (c e4) (c u0) (c u1)),
    .mul (c re) (sub (c m) (.add (c j) (.add (c b0) (c b1)))),
    -- next request (same τ, cid + 1) or a param row or padding
    mul3 (c re) (n kS) (notE (n fQ)),
    .mul (.mul (c re) (n fQ)) (sub (n cid) (.add (c cid) (k 1))) ] ++
  instCols.map (fun x => .mul (.mul (c re) (n fQ)) (sub (n x) (c x))) ++
  [ -- values: Q·40 + rem = D·(pos + 1), rem < 40
    .mul (c kS) (sub (.add (smul 40 (c Q0)) r0E) (.mul (c dd) (.add posE (k 1)))),
    .mul (c kS) (sub (.add (smul 40 (c Q1)) r1E) (.mul (c dd) (.add posE (k 2)))),
    .mul (c (rb0 5)) (c (rb0 4)), .mul (c (rb0 5)) (c (rb0 3)),
    .mul (c (rb1 5)) (c (rb1 4)), .mul (c (rb1 5)) (c (rb1 3)),
    .mul (c kS) (sub (c cm) (.add (.mul (c b0) val0) (.mul (notE (c b0)) (c cur)))),
    -- zk0 = [key = 0]
    .mul (c kS) (sub (c zk0) (notE (.mul (c key) (c ikey)))),
    .mul (c key) (c zk0) ]

def eE : Expr := .add (smul 64 (c cid)) (c j)
def aL : Expr := .add (smul 16384 (c tau)) (c link)

def interactions : List Interaction :=
  [ { bus := B_SPAR, mult := [c kP], send := false,
      msg := [c tau, k 1, c nn, c (q 0), c (q 1), c (q 2), c (q 3), c (q 4), c clo, k 0, k 0] },
    { bus := B_SRAW, mult := [c fQ], send := false,
      msg := [c tau, c clo, c chi, c s, c r, c (q 0), c (q 1), c (q 2), c (q 3), c (q 4)] },
    { bus := B_SINC, mult := [c us0], send := true,
      msg := [c tau, eE, sub val0 (c cur), sub (sub (c m) (c j)) (k 1), c s, c r, c link] },
    { bus := B_SINC, mult := [c us1], send := true,
      msg := [c tau, .add eE (c b0), sub val1 (c cm), sub (sub (sub (c m) (c j)) (c b0)) (k 1),
              c s, c r, c link] },
    { bus := B_SPUSH, mult := [c re], send := true,
      msg := [c tau, c key, c zk0, c cid, smul 64 (c cid)] },
    { bus := B_SOP, mult := [c re], send := true,
      msg := [aL, .add (c cid) (k 1), k OP_READ, c key, c key, k 0, k 0, k 0] } ]

def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.Sched.Scan
