import ZkFormal.Chacha.Rng.Table
import ZkFormal.NearV3.Sched.Tables.Dist

/-!
# ZkFormal.NearV3.Sched.Tables.Scan — the scan rows of `ssdV3`: request bitmaps → increases

Width cut B: the scan family shares the table `ssdV3` (`Tables/ScanDist.lean`) with the
distribute family; its sections come first. Per instance τ with requests: a **param row** (`kP`,
public `SPAR (τ, 1, base₀..₂, D₀..₂, n, 0, 0)`, `D = max_single_grant − base`), then each
converted request `cid = 0, 1, …` (public `SPAR (τ, 2, bm₀ … bm₄, cid_lo, cid_hi, s, r)`, only
requests with a set bit are published) as
**20 rows**, row `(y, u)` holding bitmap bits `2(4y+u)` and `2(4y+u)+1`. The bytes sit in a
register `q₀ … q₄` that is consumed two bits per row (`q₀ = b₀ + 2b₁ + 4·q₀'`, exhausted at the
byte end, then rotated), so the bits are exactly the bitmap. For a set bit at position `c`:
`v[c] = base + ⌊D(c+1)/40⌋` (remainders `< 40` by bits), the increase is `v[c] − cur`
(`cur` = value of the previous set bit, `base` first, `Spec/Conv`), sent as
`INC (τ, cid·64 + j, inc, m − j − 1, s, r, link)` with multiplicity `used ≤ bit`
(`m` = number of set bits, checked at the request end). At the request end the initial push
`(τ, key, [key = 0], cid, cid·64)` is sent with a memory READ of the link at time `cid + 1`
(the merged `SOP` send `(τ·2^14 + link, cid + kS, kS, key, key + bvz, 0, 0, 0)`, `bvz = 0`).

Multiplexed columns: the param row keeps `base₀..₂` in `q₀..q₂`, `D₀..₂` in `q₃, q₄, clo` and
`n` in `chi`. Constraints that would bind distribute rows (`(y − 4)·e4`, `re = e4·u₀·u₁`, the
remainder bounds `< 40`, `key·zk0`) are gated by `kS`.
-/

namespace ZkFormal.NearV3.Sched.Scan

open ZkFormal.Air ZkFormal.Chacha.Table.E
open ZkFormal.Chacha.Table (boolC)

/-! Columns: the scan names point into the physical layout of `ssdV3` (owned by
`Tables/Dist.lean`). The record window `f₀ … f₈` holds `q₀ … q₄, clo, chi, s, r`; the
quotients and their bits share the distribute quotient columns (`Q₀ = q1`, `Q₁ = q2`, the 23-bit
and 6-bit decompositions are the same constraints); the remainder bits `rb0, rb1` are the
distribute `rb1, rb2` (so `Dist.r1, Dist.r2` hold the remainders on request rows); the scan bits
`b₀ … zk0` sit on the distribute bits `bt1`; `fQ, re, us0, us1` are scan-only columns (zero on
distribute rows). -/

def act : Nat := Dist.act
def kP : Nat := Dist.kP
def kS : Nat := Dist.kS
def kSh : Nat := Dist.kSh
def kGH : Nat := Dist.kGH
def kC : Nat := Dist.kC
def tau : Nat := Dist.tau
def nn : Nat := Dist.nn
def q (i : Nat) : Nat := Dist.fw i
def clo : Nat := Dist.fw 5
def chi : Nat := Dist.fw 6
def s : Nat := Dist.fw 7
def r : Nat := Dist.fw 8
def base : Nat := Dist.a
/-- Zero on shard rows (the merged `SOP` time is `cid + kS`). -/
def cid : Nat := Dist.b
/-- Zero on shard rows (the merged `SOP` `vin` is `key`). -/
def key : Nat := Dist.s
def dd : Nat := Dist.r
/-- The merged `SOP` address word (`Dist.adr` on shard rows). -/
def link : Nat := Dist.adr
/-- Zero on scan rows (the merged `SOP` value is `key + bvz`; `Dist.bv` on shard rows). -/
def bvz : Nat := Dist.bv
def y : Nat := Dist.N2
def iy : Nat := Dist.L2
def Q0 : Nat := Dist.q1
def Q1 : Nat := Dist.q2
def b0 : Nat := Dist.bt1 0
def b1 : Nat := Dist.bt1 1
def u0 : Nat := Dist.bt1 2
def u1 : Nat := Dist.bt1 3
def e4 : Nat := Dist.bt1 4
def zk0 : Nat := Dist.bt1 5
def cur : Nat := Dist.da
def cm : Nat := Dist.db
def ikey : Nat := Dist.ig1
def j : Nat := Dist.cx
def m : Nat := Dist.cy
def rb0 (i : Nat) : Nat := Dist.rb1 i
def rb1 (i : Nat) : Nat := Dist.rb2 i
/-- Range checks: bits of `Q0`, `Q1` (23 each). -/
def qb0 (i : Nat) : Nat := Dist.qb1 i
def qb1 (i : Nat) : Nat := Dist.qb2 i
def fQ : Nat := 115
def re : Nat := 116
def us0 : Nat := 117
def us1 : Nat := 118
def width : Nat := Dist.width

def mul3 (a b d : Expr) : Expr := .mul (.mul a b) d
def notE (e : Expr) : Expr := sub (k 1) e

/-- Bit columns that are distribute bit columns too (their booleanity is shared). -/
def sharedBool : List Nat :=
  [act, kP, kS, kSh, kGH, kC, b0, b1, u0, u1, e4, zk0] ++
  (List.range 6).map rb0 ++ (List.range 6).map rb1 ++ (List.range 23).map qb0 ++ (List.range 23).map qb1
/-- Scan-only bit columns (zero on distribute rows). -/
def ownBool : List Nat := [fQ, re, us0, us1]
def boolCols : List Nat := sharedBool ++ ownBool

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

/-- Constraints the scan family shares with the distribute family (`ScanDist.shared_sub`): the
booleanity of the shared bit columns, the kind constraints, and the quotient decompositions
(`Q₀ = q1`, `Q₁ = q2`, 23 bits). -/
def shared : List Expr :=
  sharedBool.map boolC ++ Dist.cCommon ++
  [ sub (c Q0) (ZkFormal.Chacha.Rng.Table.num qb0 23), sub (c Q1) (ZkFormal.Chacha.Rng.Table.num qb1 23) ]

/-- The scan family's own constraints besides booleanity. Constraints that would bind
distribute rows are gated by `kS`. -/
def body : List Expr :=
  [ .mul (c fQ) (notE (c kS)),
    .mul (c re) (notE (c kS)),
    .mul (c us0) (notE (c b0)), .mul (c us1) (notE (c b1)),
    .mul (c us0) (notE (c kS)), .mul (c us1) (notE (c kS)),
    -- the merged `SOP` value window is zero on scan rows
    .mul (c kS) (c bvz),
    -- param row (`n` in the record window column `chi`)
    .mul (c kP) (sub (c chi) (c nn)),
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
    mul3 (c kS) (sub (c y) (k 4)) (c e4),
    .mul (c kS) (sub (c re) (mul3 (c e4) (c u0) (c u1))),
    .mul (c re) (sub (c m) (.add (c j) (.add (c b0) (c b1)))),
    -- next request (same τ, cid + 1) or a param row or padding
    mul3 (c re) (n kS) (notE (n fQ)),
    .mul (.mul (c re) (n fQ)) (sub (n cid) (.add (c cid) (k 1))) ] ++
  instCols.map (fun x => .mul (.mul (c re) (n fQ)) (sub (n x) (c x))) ++
  [ -- values: Q·40 + rem = D·(pos + 1), rem < 40
    .mul (c kS) (sub (.add (smul 40 (c Q0)) r0E) (.mul (c dd) (.add posE (k 1)))),
    .mul (c kS) (sub (.add (smul 40 (c Q1)) r1E) (.mul (c dd) (.add posE (k 2)))),
    mul3 (c kS) (c (rb0 5)) (c (rb0 4)), mul3 (c kS) (c (rb0 5)) (c (rb0 3)),
    mul3 (c kS) (c (rb1 5)) (c (rb1 4)), mul3 (c kS) (c (rb1 5)) (c (rb1 3)),
    .mul (c kS) (sub (c cm) (.add (.mul (c b0) val0) (.mul (notE (c b0)) (c cur)))),
    -- zk0 = [key = 0]
    .mul (c kS) (sub (c zk0) (notE (.mul (c key) (c ikey)))),
    mul3 (c kS) (c key) (c zk0) ]

/-- The scan family's own constraints (in `ScanDist.constraints` after the distribute ones). -/
def own : List Expr := ownBool.map boolC ++ body

/-- The scan family's constraints (quotients `< 2^23` by `shared`: `40·Q + rem = D·(pos+1)` is
an integer division). -/
def constraints : List Expr := shared ++ own

def eE : Expr := .add (smul 64 (c cid)) (c j)
def aL : Expr := .add (smul 16384 (c tau)) (c link)

/-! The scan family's interactions are in `ScanDist.interactions`: the merged `SPAR` receive
(tags 1, 2) and `SOP` send (READ), and its own `SINC` ×2, `SPUSH`. -/

end ZkFormal.NearV3.Sched.Scan
