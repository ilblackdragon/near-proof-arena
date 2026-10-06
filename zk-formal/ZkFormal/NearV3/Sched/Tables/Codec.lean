import ZkFormal.Chacha.Rng.Table
import ZkFormal.NearV3.Sched.Ids

/-!
# ZkFormal.NearV3.Sched.Tables.Codec — `schV3`: the `0x0f` state bytes and the per-link pass

One row per byte of `BandwidthSchedulerState::V1` borsh, the previous value (`bpre`, when present)
and the new value (`bpost`) in lockstep (both canonical: the layout's `N = n²` links sender-major,
Canon0f), then the sanity-hash input:

| rows | kind | content |
|---|---|---|
| 5 | `kH` | `[0, N₀, N₁, 0, 0]` (tag, `u32 N`); the first (`kF`) receives `SPAR (τ, 0, n, N₀, N₁, base, fair)` and `S0F (τ, present, vid)` |
| `24·N` | `kR` | record `k`: sender id (8), receiver id (8), allowance (8) bytes; field flags `fS, fR, fA`, byte `g` |
| 32 | `kZ` | previous sanity hash (pre) / new sanity hash (post, the SHA digest) |
| 32 | `kA` | `sha256(all_shards)` bytes (public), the second half of the SHA input |

* **Ids**: the 16 id bytes of record `k` are the same in every instance; each is received from
  instance `τ − 1` and sent to `τ + 1` on `SDL (τ, k, o, b)` (the public bus sends instance 0's
  and receives instance `K + 1`'s), and the pre byte equals the post byte (canonical prev).
* **Allowance bytes**: pre: low three bytes accumulated (`ap`), `big` = some higher byte
  nonzero; post: three bytes of the final allowance `afin` (range-checked by bits), higher bytes 0.
* **Link pass** at the record end (`rend`): `a1 = big ? MA : min(ap + fair, MA)` (comparator at
  byte 2), `a2 = a1 − al·base`, `g2 = al·base`; memory INIT `(link, a2, g2, al)`, FIN
  `(afin, gfin)`; the grid's `(al, gb)`; in instance 0 the forwarding demand `ft ≤ gfin + gb`.
* **Sanity hash**: SHA message `11 + 16τ` = `prev hash ‖ sha256(all_shards)` (64 bytes; zeros if
  absent), its digest (received at the last record row into the shift register `reg`) is the
  post hash.

Multiplexed columns: `reg` holds the header bytes and the param bytes on the header rows.
-/

namespace ZkFormal.NearV3.Sched.Codec

open ZkFormal.Air ZkFormal.Chacha.Table.E
open ZkFormal.Chacha.Table (boolC)

def act : Nat := 0
def kH : Nat := 1
def kR : Nat := 2
def kZ : Nat := 3
def kA : Nat := 4
def kF : Nat := 5
def tau : Nat := 6
def pos : Nat := 7
def pres : Nat := 8
def vid : Nat := 9
def nn : Nat := 10
def NN : Nat := 11
def base : Nat := 12
def fair : Nat := 13
def bpre : Nat := 14
def bpost : Nat := 15
def pbit (i : Nat) : Nat := 16 + i
def kidx : Nat := 24
def klo : Nat := 25
def khi : Nat := 26
def fS : Nat := 27
def fR : Nat := 28
def fA : Nat := 29
def g : Nat := 30
def ig7 : Nat := 31
def e7 : Nat := 32
def ig2 : Nat := 33
def e2 : Nat := 34
def lowf : Nat := 35
def wt : Nat := 36
def ap : Nat := 37
def big : Nat := 38
def ib : Nat := 39
def nzb : Nat := 40
def apost : Nat := 41
def ikl : Nat := 42
def ekl : Nat := 43
def ihp : Nat := 44
def ehp : Nat := 45
def sj : Nat := 46
def isj : Nat := 47
def esj : Nat := 48
def bsha : Nat := 49
def fb (i : Nat) : Nat := 50 + i
def reg (i : Nat) : Nat := 53 + i
def al : Nat := 85
def a1 : Nat := 86
def cb : Nat := 87
def afin : Nat := 88
def gfin : Nat := 89
def gb : Nat := 90
def itz : Nat := 91
def zt : Nat := 92
def cx : Nat := 93
def cy : Nat := 94
def cbit : Nat := 95
def cg : Nat := 96
def rend : Nat := 97
def a2 : Nat := 98
def g2 : Nat := 99
def vbg : Nat := 100
def fwg : Nat := 101
def pm0 : Nat := 102
def pm1 : Nat := 103
def dgg : Nat := 104
def bF : Nat := 105
def width : Nat := 106

/-- `max_allowance` (PV 86). -/
def MA : Nat := 4500000
/-- SHA message kind of the sanity hash (`msgId 11 τ`). -/
def K_SCH : Nat := 11

def mul3 (x y w : Expr) : Expr := .mul (.mul x y) w
def notE (e : Expr) : Expr := sub (k 1) e

/-- `flag = [x = 0]` on rows where `gate = 1`, and `flag = 0` elsewhere. -/
def isZ (gate x : Expr) (inv flag : Nat) : List Expr :=
  [ .mul gate (sub (c flag) (notE (.mul x (c inv)))),
    .mul gate (.mul x (c flag)),
    .mul (notE gate) (c flag) ]

def boolCols : List Nat :=
  [act, kH, kR, kZ, kA, kF, pres, fS, fR, fA, e7, e2, lowf, nzb, ekl, ehp, esj, al, cb, zt,
   cbit, cg, rend, vbg, fwg, dgg, bF] ++ (List.range 8).map pbit

/-- Rows carrying the encoding (pre and post bytes). -/
def encG : Expr := .add (c kH) (.add (c kR) (c kZ))
def pbitsE : Expr := ZkFormal.Chacha.Rng.Table.num pbit 8
def oE : Expr := .add (smul 8 (c fR)) (c g)
def aLE : Expr := .add (smul 16384 (c tau)) (c kidx)
def ftE : Expr := .add (c (fb 0)) (.add (smul 256 (c (fb 1))) (smul 65536 (c (fb 2))))
/-- Not the last row of an instance block. -/
def gT : Expr := sub (c act) (.mul (c kA) (c esj))
def instCols : List Nat := [tau, pres, vid, nn, NN, base, fair]

def cKind : List Expr :=
  boolCols.map boolC ++
  [ sub (c act) (.add (c kH) (.add (c kR) (.add (c kZ) (c kA)))),
    sub (c kR) (.add (c fS) (.add (c fR) (c fA))),
    .mul (c kF) (notE (c kH)),
    .mul .isLast (c act),
    mul3 .isTransition (notE (c act)) (n act),
    .mul .isFirst (.mul (c act) (notE (c kF))) ] ++
  isZ (c kR) (sub (c g) (k 7)) ig7 e7 ++
  isZ (c fA) (sub (c g) (k 2)) ig2 e2 ++
  isZ (c kR) (sub (c kidx) (sub (c NN) (k 1))) ikl ekl ++
  isZ (c kH) (sub (c pos) (k 4)) ihp ehp ++
  isZ (.add (c kZ) (c kA)) (sub (c sj) (.add (k 31) (smul 32 (c kA)))) isj esj ++
  isZ (c act) (c tau) itz zt ++
  [ -- instance constants and the byte position
    .mul gT (sub (n tau) (c tau)), .mul gT (sub (n pres) (c pres)), .mul gT (sub (n vid) (c vid)),
    .mul gT (sub (n nn) (c nn)), .mul gT (sub (n NN) (c NN)), .mul gT (sub (n base) (c base)),
    .mul gT (sub (n fair) (c fair)),
    .mul encG (sub (n pos) (.add (c pos) (k 1))),
    mul3 (c kA) (c esj) (.mul (n act) (notE (n kF))),
    -- bytes: post bytes are bytes; pre = 0 when absent
    .mul encG (sub (c bpost) pbitsE),
    .mul (notE (c pres)) (c bpre),
    sub (c vbg) (.mul (c pres) encG),
    -- header
    .mul (c kF) (c pos),
    .mul (c kF) (c (reg 0)), .mul (c kF) (c (reg 3)), .mul (c kF) (c (reg 4)),
    .mul (c kF) (sub (c NN) (.add (c (reg 1)) (smul 256 (c (reg 2))))),
    .mul (c kF) (sub (c NN) (.mul (c nn) (c nn))),
    .mul (c kF) (sub (c base) (.add (c (reg 5)) (.add (smul 256 (c (reg 6))) (smul 65536 (c (reg 7)))))),
    .mul (c kF) (sub (c fair) (.add (c (reg 8)) (.add (smul 256 (c (reg 9))) (smul 65536 (c (reg 10)))))),
    .mul (c kH) (sub (c bpost) (c (reg 0))),
    .mul (c kH) (sub (c bpre) (.mul (c pres) (c bpost))),
    mul3 (c kH) (notE (c ehp)) (notE (n kH)) ] ++
  (List.range 31).map (fun i => mul3 (c kH) (notE (c ehp)) (sub (n (reg i)) (c (reg (i + 1))))) ++
  [ -- header → first record
    .mul (c ehp) (notE (n fS)), .mul (c ehp) (n kidx), .mul (c ehp) (n g) ]

def cRec : List Expr :=
  [ .mul (c kR) (sub (c kidx) (.add (c klo) (smul 256 (c khi)))),
    -- inside a field
    mul3 (c kR) (notE (c e7)) (sub (n g) (.add (c g) (k 1))),
    mul3 (c kR) (notE (c e7)) (sub (n fS) (c fS)),
    mul3 (c kR) (notE (c e7)) (sub (n fR) (c fR)),
    mul3 (c kR) (notE (c e7)) (sub (n fA) (c fA)),
    mul3 (c kR) (notE (c e7)) (sub (n kidx) (c kidx)),
    -- field ends
    .mul (c e7) (n g),
    mul3 (c e7) (c fS) (notE (n fR)), mul3 (c e7) (c fS) (sub (n kidx) (c kidx)),
    mul3 (c e7) (c fR) (notE (n fA)), mul3 (c e7) (c fR) (sub (n kidx) (c kidx)),
    sub (c rend) (.mul (c fA) (c e7)),
    mul3 (c rend) (notE (c ekl)) (notE (n fS)),
    mul3 (c rend) (notE (c ekl)) (sub (n kidx) (.add (c kidx) (k 1))),
    sub (c dgg) (.mul (c rend) (c ekl)),
    .mul (c dgg) (notE (n kZ)), .mul (c dgg) (n sj) ] ++
  (List.range 32).map (fun i => .mul (c dgg) (sub (n (reg i)) (c (reg i)))) ++
  [ -- id bytes: pre = post
    .mul (.add (c fS) (c fR)) (sub (c bpre) (.mul (c pres) (c bpost))),
    -- allowance field: start values (set by the receiver field's last row)
    mul3 (c e7) (c fR) (n ap), mul3 (c e7) (c fR) (n big), mul3 (c e7) (c fR) (n apost),
    mul3 (c e7) (c fR) (sub (n wt) (k 1)), mul3 (c e7) (c fR) (sub (n lowf) (k 1)),
    -- accumulation inside the field
    .mul (sub (c fA) (c rend)) (sub (n ap) (.add (c ap) (mul3 (c lowf) (c wt) (c bpre)))),
    .mul (sub (c fA) (c rend)) (sub (n apost) (.add (c apost) (mul3 (c lowf) (c wt) (c bpost)))),
    .mul (sub (c fA) (c rend)) (sub (n big) (.add (c big) (mul3 (notE (c big)) (notE (c lowf)) (c nzb)))),
    .mul (sub (c fA) (c rend)) (sub (n wt) (smul 256 (c wt))),
    .mul (sub (c fA) (c rend)) (sub (n lowf) (.mul (c lowf) (notE (c e2)))),
    mul3 (c fA) (notE (c lowf)) (c bpost),
    .mul (c fA) (sub (c nzb) (.mul (c bpre) (c ib))),
    .mul (c fA) (.mul (c bpre) (notE (c nzb))),
    -- a1: comparator at byte 2 (cb = [MA ≤ ap + fair]), carried to the record end
    mul3 (c fA) (c e2) (sub (c cx) (.add (.add (c ap) (.mul (c wt) (c bpre))) (c fair))),
    mul3 (c fA) (c e2) (sub (c cy) (k MA)),
    mul3 (c fA) (c e2) (sub (c cbit) (c cb)),
    .mul (sub (c fA) (c rend)) (.mul (notE (c lowf)) (sub (n cb) (c cb))),
    mul3 (c fA) (c e2) (sub (n cb) (c cb)),
    -- record end
    .mul (c rend) (sub (c bF) (.add (c big) (.mul (notE (c big)) (c nzb)))),
    .mul (c rend) (sub (c a1) (.add (smul MA (c bF))
      (.mul (notE (c bF)) (.add (smul MA (c cb)) (.mul (notE (c cb)) (.add (c ap) (c fair))))))),
    .mul (c rend) (sub (c a2) (sub (c a1) (.mul (c al) (c base)))),
    .mul (c rend) (sub (c g2) (.mul (c al) (c base))),
    .mul (c rend) (sub (c apost) (c afin)),
    -- forwarding (instance 0)
    sub (c fwg) (.mul (c rend) (c zt)),
    .mul (c fwg) (sub (c cx) (.add (c gfin) (c gb))),
    .mul (c fwg) (sub (c cy) ftE),
    .mul (c fwg) (sub (c cbit) (k 1)),
    sub (c cg) (.add (.mul (c fA) (c e2)) (c fwg)) ]

def cTrl : List Expr :=
  [ -- Z rows: post = digest (shift register), SHA input = pre (prev hash or zeros)
    .mul (c kZ) (sub (c bpost) (c (reg 0))),
    .mul (c kZ) (sub (c bsha) (c bpre)),
    mul3 (c kZ) (notE (c esj)) (notE (n kZ)),
    mul3 (c kZ) (notE (c esj)) (sub (n sj) (.add (c sj) (k 1))),
    mul3 (c kZ) (c esj) (notE (n kA)),
    mul3 (c kZ) (c esj) (sub (n sj) (k 32)),
    -- A rows: SHA input = public `sha256(all_shards)` bytes
    mul3 (c kA) (notE (c esj)) (notE (n kA)),
    mul3 (c kA) (notE (c esj)) (sub (n sj) (.add (c sj) (k 1))),
    .mul (c kA) (sub (c pm0) (sub (c sj) (k 32))),
    .mul (c kA) (sub (c pm1) (c bsha)),
    .mul (c kA) (c (fb 0)), .mul (c kA) (c (fb 1)), .mul (c kA) (c (fb 2)),
    .mul (c fwg) (sub (c pm0) (c klo)),
    .mul (c fwg) (sub (c pm1) (c khi)) ] ++
  (List.range 31).map (fun i => mul3 (c kZ) (notE (c esj)) (sub (n (reg i)) (c (reg (i + 1)))))

def constraints : List Expr := cKind ++ cRec ++ cTrl

def shaId : Expr := .add (k K_SCH) (smul 16 (c tau))

def interactions : List Interaction :=
  [ { bus := ZkFormal.NearV3.B_VBYTES, mult := [c vbg], send := true, msg := [c vid, c pos, c bpre] },
    { bus := B_SPOST, mult := [encG], send := true, msg := [c tau, c pos, c bpost] },
    { bus := ZkFormal.Near.B_BYTES, mult := [.add (c kZ) (c kA)], send := true, msg := [shaId, c sj, c bsha] },
    { bus := ZkFormal.Near.B_DIGEST, mult := [c dgg], send := false,
      msg := [shaId, k 64] ++ (List.range 32).map fun i => c (reg i) },
    { bus := B_S0F, mult := [c kF], send := false, msg := [c tau, c pres, c vid] },
    { bus := B_SPAR, mult := [c kF], send := false,
      msg := [c tau, k 0, c nn, c (reg 1), c (reg 2), c (reg 5), c (reg 6), c (reg 7), c (reg 8),
              c (reg 9), c (reg 10)] },
    { bus := B_SDL, mult := [.add (c fS) (c fR)], send := false, msg := [c tau, c klo, c khi, oE, c bpost] },
    { bus := B_SDL, mult := [.add (c fS) (c fR)], send := true,
      msg := [.add (c tau) (k 1), c klo, c khi, oE, c bpost] },
    { bus := B_SPUBB, mult := [.add (c kA) (c fwg)], send := false,
      msg := [c tau, .add (smul 2 (c kA)) (smul 4 (c fwg)), c pm0, c pm1, c (fb 0), c (fb 1), c (fb 2)] },
    { bus := B_SOP, mult := [c rend], send := true,
      msg := [aLE, k 0, k OP_INIT, c al, c a2, c g2, k 0, k 0] },
    { bus := B_SFIN, mult := [c rend], send := false, msg := [aLE, c afin, c gfin] },
    { bus := B_SDG, mult := [c rend], send := false, msg := [c tau, c kidx, c al, c gb] },
    { bus := B_SCMP, mult := [c cg], send := true, msg := [c cx, c cy, c cbit] } ]

def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.Sched.Codec
