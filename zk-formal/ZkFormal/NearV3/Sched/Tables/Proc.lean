import ZkFormal.Chacha.Rng.Table
import ZkFormal.NearV3.Sched.Ids

/-!
# ZkFormal.NearV3.Sched.Tables.Proc — `sprV3`: rounds of `process_bandwidth_requests`

Per instance τ (in order `τ = 0, 1, …`): a **key block** of 16 rows assembling the ChaCha key
limbs `L0 … L15` from public records `(τ, 3, k, lo, hi)` (a rotating register), then the
**rounds** (`Spec/Loop.process_rounds`), each a **header** row followed by its **entries**
(`x = 0 … Lr − 1`). An entry row is at once
* the bucket entry `x`: receives the push `(τ, K, z, ts, ein)`, sends `ein` as shuffle input `x`;
  `ts` strictly increasing, the last one `< T` (comparator);
* the processing step at time `t = T + x`: receives shuffle output `eout`, its increase
  `INC (τ, eout, inc, rem, s, r, link)`, does the three memory GRANT ops (sender, receiver, link)
  with `ok = cS·cR·cL`, and re-pushes `(τ, alOut, zn, t, eout + 1)` iff `ok ∧ rem ≠ 0`.

The header receives the shuffle header `(lid, key, kst, Lr, kend)` (lane v3-chacha `busShuf`),
chains the RNG positions (`kst` = previous `kend`, 0 at the first round) and the times
(`T` = previous `T + Lr`, `T0` first), and checks the round order: a positive key is below the
previous key (sentinel `2^24` after the key block) and follows no 0-round; a 0-round has
`z = previous z + 1` (previous `z` = 0 for positive rounds and after the key block).

Multiplexed columns: key rows use `sbIn, sbOut` as the record bytes `lo, hi`.
-/

namespace ZkFormal.NearV3.Sched.Proc

open ZkFormal.Air ZkFormal.Chacha.Table.E
open ZkFormal.Chacha.Table (boolC)

def act : Nat := 0
def kK : Nat := 1
def kH : Nat := 2
def kE : Nat := 3
def tau : Nat := 4
def colL (i : Nat) : Nat := 5 + i
def kc : Nat := 21
def kl : Nat := 22
def ikc : Nat := 23
def kq : Nat := 24
def Tq : Nat := 25
def Kq : Nat := 26
def zq : Nat := 27
def K : Nat := 28
def z : Nat := 29
def zk : Nat := 30
def iK : Nat := 31
def kend : Nat := 32
def Lr : Nat := 33
def T : Nat := 34
def x : Nat := 35
def ts : Nat := 36
def ein : Nat := 37
def eout : Nat := 38
def inc : Nat := 39
def rem : Nat := 40
def irem : Nat := 41
def lastf : Nat := 42
def s : Nat := 43
def r : Nat := 44
def link : Nat := 45
def sbIn : Nat := 46
def sbOut : Nat := 47
def rbIn : Nat := 48
def rbOut : Nat := 49
def alIn : Nat := 50
def alOut : Nat := 51
def cS : Nat := 52
def cR : Nat := 53
def cL : Nat := 54
def ok : Nat := 55
def ia : Nat := 56
def za : Nat := 57
def zn : Nat := 58
def pm : Nat := 59
def le : Nat := 60
def cg : Nat := 61
def cx : Nat := 62
def cy : Nat := 63
def width : Nat := 64

/-- Sentinel previous key after the key block (above every allowance). -/
def KSENT : Nat := 16777216

def mul3 (a b d : Expr) : Expr := .mul (.mul a b) d
def notE (e : Expr) : Expr := sub (k 1) e

def boolCols : List Nat := [act, kK, kH, kE, kl, zk, lastf, cS, cR, cL, ok, za, pm, le, cg]

/-- Rows continuing the current round into the next row (header, or a non-last entry). -/
def gR : Expr := sub (.add (c kH) (c kE)) (c le)
/-- Rows after which a new key block may start (last key row, last entry). -/
def gB : Expr := .add (c kl) (c le)

def tE : Expr := .add (c T) (c x)
def lidE : Expr := .add (smul 4194304 (c tau)) (c T)
def aS : Expr := .add (smul 16384 (c tau)) (.add (k 4096) (c s))
def aR : Expr := .add (smul 16384 (c tau)) (.add (k 8192) (c r))
def aL : Expr := .add (smul 16384 (c tau)) (c link)

/-- Round constants copied from the header to its entries. -/
def roundCols : List Nat := [K, z, zk, T, Lr, kend, tau]
/-- Instance carries (key rows to the first header; entries to the next header). -/
def instCols : List Nat := [kq, Tq, Kq, zq, tau]

def cKind : List Expr :=
  boolCols.map boolC ++
  [ sub (c act) (.add (c kK) (.add (c kH) (c kE))),
    .mul .isLast (c act),
    mul3 .isTransition (notE (c act)) (n act),
    .mul .isFirst (.mul (c act) (notE (c kK))),
    .mul .isFirst (c kc),
    .mul .isFirst (c tau) ]

def cKey : List Expr :=
  [ -- kl = [kc = 15]
    sub (c kl) (notE (.mul (sub (c kc) (k 15)) (c ikc))),
    .mul (sub (c kc) (k 15)) (c kl),
    .mul (c kl) (notE (c kK)),
    -- inside a block
    .mul (sub (c kK) (c kl)) (notE (n kK)),
    .mul (sub (c kK) (c kl)) (sub (n kc) (.add (c kc) (k 1))),
    .mul (sub (c kK) (c kl)) (sub (n tau) (c tau)),
    -- a new block starts at kc = 0 with τ + 1
    mul3 gB (n kK) (n kc),
    mul3 gB (n kK) (sub (n tau) (.add (c tau) (k 1))),
    -- the register: limb kc = lo + 256 hi, rotate
    .mul (c kK) (sub (c (colL 0)) (.add (c sbIn) (smul 256 (c sbOut)))),
    -- instance initial values
    .mul (c kK) (c kq), .mul (c kK) (sub (c Tq) (k T0)), .mul (c kK) (sub (c Kq) (k KSENT)),
    .mul (c kK) (c zq) ] ++
  (List.range 16).map (fun i => .mul (c kK) (sub (n (colL i)) (c (colL ((i + 1) % 16))))) ++
  (List.range 16).map (fun i => mul3 (.add (c kH) (c kE)) (notE (n kK)) (sub (n (colL i)) (c (colL i))))

def cHdr : List Expr :=
  [ .mul (c kH) (sub (c T) (c Tq)),
    .mul (c kH) (sub (n Tq) (.add (c T) (c Lr))),
    .mul (c kH) (sub (n kq) (c kend)),
    .mul (c kH) (sub (n Kq) (c K)),
    .mul (c kH) (sub (n zq) (c z)),
    mul3 (c kH) (notE (c zk)) (c z),
    mul3 (c kH) (c zk) (c K),
    mul3 (c kH) (notE (c zk)) (sub (.mul (c K) (c iK)) (k 1)),
    mul3 (c kH) (c zk) (sub (c z) (.add (c zq) (k 1))),
    mul3 (c kH) (notE (c zk)) (c zq),
    -- header → entry 0
    .mul (c kH) (notE (n kE)),
    .mul (c kH) (n x),
    -- headers follow a block end or a round end
    .mul (n kH) (notE gB),
    -- entries follow a continuing row
    .mul (n kE) (notE gR) ] ++
  roundCols.map (fun col => .mul gR (sub (n col) (c col))) ++
  [ .mul gR (notE (n kE)) ] ++
  -- instance carries through entries and key rows (not into a new block)
  instCols.map (fun col => mul3 (.add (c kE) (c kK)) (notE (n kK)) (sub (n col) (c col)))

def cEnt : List Expr :=
  [ .mul (c le) (notE (c kE)),
    .mul (c le) (sub (.add (c x) (k 1)) (c Lr)),
    mul3 (c kE) (notE (c le)) (sub (n x) (.add (c x) (k 1))),
    -- last = [rem = 0]
    .mul (c kE) (sub (c lastf) (notE (.mul (c rem) (c irem)))),
    .mul (c rem) (c lastf),
    -- ok = cS·cR·cL
    .mul (c kE) (sub (c ok) (mul3 (c cS) (c cR) (c cL))),
    -- za = [alOut = 0], zn = za·(z + 1)
    .mul (c kE) (sub (c za) (notE (.mul (c alOut) (c ia)))),
    mul3 (c kE) (c alOut) (c za),
    .mul (c kE) (sub (c zn) (.mul (c za) (.add (c z) (k 1)))),
    -- push gate
    sub (c pm) (mul3 (c kE) (c ok) (notE (c lastf))),
    -- comparator gate and operands
    sub (c cg) (.add (.mul (c kH) (notE (c zk))) (c kE)),
    .mul (c kH) (sub (c cx) (c Kq)),
    .mul (c kH) (sub (c cy) (.add (c K) (k 1))),
    .mul (c kE) (sub (c cy) (.add (c ts) (k 1))),
    .mul (c kE) (sub (c cx) (.add (.mul (c le) (c T)) (.mul (notE (c le)) (n ts)))) ]

def constraints : List Expr := cKind ++ cKey ++ cHdr ++ cEnt

def keyMsg : List Expr := (List.range 16).map fun i => c (colL i)

def interactions : List Interaction :=
  [ { bus := B_SPUBB, mult := [c kK], send := false, msg := [c tau, k TAG_KEY, c kc, c sbIn, c sbOut, k 0, k 0] },
    { bus := B_SSHUF, mult := [c kH], send := false, msg := [lidE] ++ keyMsg ++ [c kq, c Lr, c kend] },
    { bus := B_SCMP, mult := [c cg], send := true, msg := [c cx, c cy, k 1] },
    { bus := B_SPUSH, mult := [c kE], send := false, msg := [c tau, c K, c z, c ts, c ein] },
    { bus := B_SSIN, mult := [c kE], send := true, msg := [lidE, c x, c ein] },
    { bus := B_SSOUT, mult := [c kE], send := false, msg := [lidE, c x, c eout] },
    { bus := B_SINC, mult := [c kE], send := false,
      msg := [c tau, c eout, c inc, c rem, c s, c r, c link] },
    { bus := B_SOP, mult := [c kE], send := true,
      msg := [aS, tE, k OP_GRANT, c sbIn, c sbOut, c inc, c ok, c cS] },
    { bus := B_SOP, mult := [c kE], send := true,
      msg := [aR, tE, k OP_GRANT, c rbIn, c rbOut, c inc, c ok, c cR] },
    { bus := B_SOP, mult := [c kE], send := true,
      msg := [aL, tE, k OP_GRANT, c alIn, c alOut, c inc, c ok, c cL] },
    { bus := B_SPUSH, mult := [c pm], send := true,
      msg := [c tau, c alOut, c zn, tE, .add (c eout) (k 1)] } ]

def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.Sched.Proc
