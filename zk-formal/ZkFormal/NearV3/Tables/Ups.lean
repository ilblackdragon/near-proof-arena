import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.IdsUps

/-!
# ZkFormal.NearV3.Tables.Ups — `upsV3`: the `0x0f` upsert (lane `v3-trie`, M7b)

Design and soundness sketch: `docs/zk-formal/UPSV3-DESIGN.md` (this file is its §3–§6 in
Lean).  One **segment per instance `τ`**, rows in this order:

* **walk rows** `W0 … W3` (`wk`; `W0 = sf`): the walk of the key `[0, 15]` (symbols `START`,
  `0`, `15`, `END`) over the chained `EDGE` / `BMAP` providers, with `walkV3`'s modes and message
  formats (`mS` step, `mK` absent by key, `mB` absent at a branch, `mD` drain).  `W0` is the
  head's `START` edge `(0, τ, START, N0, 0, DOWN)`.  The walk fixes the **path records**
  `N0, N1, N2` (by level `lv`), the terminal row `t*` (`ts1 … ts3`), its record level `D`
  (`dd0 … dd2`), its position `I` in that record (`ti0 … ti2`) and its key nibble `x` (`tX`).
  `W0` also receives `MIDROOT (τ, mid)`, `SPLEN (τ, L)` and sends `S0F (τ, present, vid)`;
  `W3` receives the new root's `DIGEST` and sends `ROOT (τ + 1, post)`.
* **value rows** (`vb`, part `j = 0`): `SPOST (τ, pos, b)` in, `BYTES (msgId 12 (8τ), pos, b)`
  out, `pos < L`.
* **node parts** (`qb`, `j = 1 … nQ ≤ 4`, bottom-up): one part per new path node `Q_j`; row
  `qpos` emits byte `qpos` of `Q_j` on `BYTES (msgId 12 (8τ + j), qpos, b)`.  A part follows
  `nodeV3`'s field grammar on `Q_j` (states `TAG … MEM`), and every byte is either **copied**
  from the part's source record `sN ∈ {N0, N1, N2}` (`UPB`, chained, at position `spos`) or
  **fresh** (tag, lengths, hex-prefix bytes, bitmap, digests of the new children / the new
  value from `DIGEST`, `memory_usage` from the two-chain `u64` arithmetic).

The **case selector** is the one-hot `cLP … cESn1` (segment constant); with the walk it fixes
the part plan (kinds `kRDB … kSPB` by position `jo1 … jo4`).  Degree 4.

Columns are aliased in two places: the walk-row message columns reuse part-constant columns
(`nN … trm` on `wk` rows; part constants are only constrained on `vb`/`qb` rows), and the
32-byte register `reg` holds, by row kind, a digest (fresh windows, `W0`, `W3`), the
`memory_usage` arithmetic temporaries (`MEM` rows), nibble bits (`TAG`/`HPF` reads) or the
`BMAP` bitmap bits (`W1`, `W2`).
-/

namespace ZkFormal.NearV3.UpsV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-! ## Layout -/

/-! ### Row kind / position -/
def act : Nat := 0
def wk : Nat := 1
def vb : Nat := 2
def qb : Nat := 3
def sf : Nat := 4
def wt1 : Nat := 5
def wt2 : Nat := 6
def wt3 : Nat := 7
def pf : Nat := 8
def pl : Nat := 9

/-! ### Segment constants (one value per instance `τ`) -/
def tau : Nat := 10
def N0 : Nat := 11
def N1 : Nat := 12
def N2 : Nat := 13
def L0 : Nat := 14
def L1 : Nat := 15
def L2 : Nat := 16
/-- case selector (one-hot): present leaf, present branch value, absent branch value, absent
branch slot, leaf split (a: leaf key ended, b: new key ended, c: nibbles differ), extension
split (`l`: new key ended inside, `n`: nibbles differ; `0`: shortened extension, `1`: old
child taken as is) -/
def cLP : Nat := 17
def cBR : Nat := 18
def cBV : Nat := 19
def cBI : Nat := 20
def cLSa : Nat := 21
def cLSb : Nat := 22
def cLSc : Nat := 23
def cESl0 : Nat := 24
def cESl1 : Nat := 25
def cESn0 : Nat := 26
def cESn1 : Nat := 27
/-- level `D` of the terminal record (one-hot) -/
def dd0 : Nat := 28
def dd1 : Nat := 29
def dd2 : Nat := 30
/-- terminal walk row `t*` (one-hot `W1 … W3`) -/
def ts1 : Nat := 31
def ts2 : Nat := 32
def ts3 : Nat := 33
/-- position `I` of the terminal in its record (one-hot `0 … 2`) -/
def ti0 : Nat := 34
def ti1 : Nat := 35
def ti2 : Nat := 36
/-- the record's key nibble `x` at the terminal (absent by key), its bits, `2^(x mod 8)` -/
def tX : Nat := 37
def xb (i : Nat) : Nat := 38 + i
def px : Nat := 42
/-- bitmap bytes of a split branch -/
def bmL : Nat := 43
def bmH : Nat := 44
def pres : Nat := 45
def vid : Nat := 46
/-- number of new nodes; length of the new root -/
def nQ : Nat := 47
def rlen : Nat := 48

/-! ### Part constants (one value per part; free on walk rows) -/
def j : Nat := 49
def kRDB : Nat := 50
def kRDE : Nat := 51
def kRLP : Nat := 52
def kRBR : Nat := 53
def kRBV : Nat := 54
def kRBI : Nat := 55
def kMVL : Nat := 56
def kMVE : Nat := 57
def kNLF : Nat := 58
def kWEX : Nat := 59
def kSPB : Nat := 60
def jo (i : Nat) : Nat := 60 + i   -- i = 1 … 4
def sd0 : Nat := 65
def sd1 : Nat := 66
def sd2 : Nat := 67
def sN : Nat := 68
def plen : Nat := 69
def qtl : Nat := 70
def qte : Nat := 71
def qtb1 : Nat := 72
def qtb2 : Nat := 73
def qhk : Nat := 74
def qodd : Nat := 75
def nokey : Nat := 76
def nochild : Nat := 77
def qlen : Nat := 78
def rootP : Nat := 79
def jm : Nat := 80
def clen : Nat := 81
/-- `memory_usage = E + max(0, A + B − C)`: outside constant `Kc` (+ `eL·L` + `eS·slen`);
inside `useA·m`, `bN·new(child)`, `bL·L`, minus `cO·old(child)`, `cS·slen`, `Cc` -/
def Kc : Nat := 82
def eL : Nat := 83
def eS : Nat := 84
def useA : Nat := 85
def bN : Nat := 86
def bL : Nat := 87
def cO : Nat := 88
def cS : Nat := 89
def Cc : Nat := 90
def neg : Nat := 91
/-- source record header: `hplen`, odd key length -/
def phk : Nat := 92
def podd : Nat := 93
/-- value slot copied; old child hash copied (split branch); bitmap adds (slot insert);
split branch: first / second window is the new leaf -/
def vcp : Nat := 94
def xcp : Nat := 95
def ba0 : Nat := 96
def ba1 : Nat := 97
def spY1 : Nat := 98
def spY2 : Nat := 99

/-! ### Walk-row aliases (part-constant columns, `wk` rows only) -/
def nN : Nat := 49
def nI : Nat := 50
def nib : Nat := 51
def nN2 : Nat := 52
def nI2 : Nat := 53
def ek : Nat := 54
def inv : Nat := 55
def hv : Nat := 56
def wbm : Nat := 57
def enter : Nat := 58
def lv0 : Nat := 59
def lv1 : Nat := 60
def lv2 : Nat := 61
def trm : Nat := 62

/-! ### Row columns -/
def qpos : Nat := 100
def b : Nat := 101
def rd : Nat := 102
def rb : Nat := 103
def spos : Nat := 104
def u : Nat := 105
def sTAG : Nat := 106
def sHPL : Nat := 107
def sHPF : Nat := 108
def sKEY : Nat := 109
def sVLEN : Nat := 110
def sVH : Nat := 111
def sBM : Nat := 112
def sCH : Nat := 113
def sMEM : Nat := 114
def fs : Nat := 115
def fe : Nat := 116
def idx : Nat := 117
def fw : Nat := 118
def lastw : Nat := 119
def wfr : Nat := 120
def tgt : Nat := 121
def wy : Nat := 122
def wn : Nat := 123
def gD : Nat := 124
def dI : Nat := 125
def dL : Nat := 126
def cp : Nat := 127
def aft : Nat := 128
def reg (i : Nat) : Nat := 129 + i
def LR (i : Nat) : Nat := 161 + i
def SR (i : Nat) : Nat := 164 + i
def gMs : Nat := 168
def gMr : Nat := 169
def rx : Nat := 170
def mBv : Nat := 171
def mCv : Nat := 172
def mS : Nat := 173
def mK : Nat := 174
def mB : Nat := 175
def width : Nat := 176

/-! ### `reg` aliases -/
/-- `MEM` rows: inside-chain byte bits, carries, outside-chain carries, carry-ins, inputs -/
def tb (i : Nat) : Nat := reg i
def cb (i : Nat) : Nat := reg (8 + i)
def cc (i : Nat) : Nat := reg (11 + i)
def ci : Nat := reg 14
def ci2 : Nat := reg 15
def X1 : Nat := reg 16
def Ein : Nat := reg 17
/-- read rows (`TAG`, `HPF`): nibble bits of `rb` -/
def hb (i : Nat) : Nat := reg i
def lb (i : Nat) : Nat := reg (4 + i)
/-- `W1`, `W2`: bitmap bits -/
def wb (i : Nat) : Nat := reg i

def states : List Nat := [sTAG, sHPL, sHPF, sKEY, sVLEN, sVH, sBM, sCH, sMEM]
def cases : List Nat := [cLP, cBR, cBV, cBI, cLSa, cLSb, cLSc, cESl0, cESl1, cESn0, cESn1]
def kinds : List Nat := [kRDB, kRDE, kRLP, kRBR, kRBV, kRBI, kMVL, kMVE, kNLF, kWEX, kSPB]

/-- Segment-constant columns. -/
def segConst : List Nat := (List.range 39).map (· + 10)
/-- Part-constant columns. -/
def partConst : List Nat := (List.range 51).map (· + 49)

/-! ## Derived expressions -/

def sumc (xs : List Nat) : Expr := sum (xs.map c)
def Lexpr : Expr := .add (c L0) (.add (smul 256 (c L1)) (smul 65536 (c L2)))
def Lb (i : Nat) : Nat := [L0, L1, L2].getD i L0
/-- `upsV3` SHA id `msgId 12 (8τ + jx)` -/
def upsId (jx : Expr) : Expr := mid K_VUPS (.add (smul 8 (c tau)) jx)
/-- walk symbol of the row (`START`, `0`, `15`, `END`) -/
def symE : Expr := .add (smul SYM_START (c sf)) (.add (smul 15 (c wt2)) (smul SYM_END (c wt3)))
/-- terminal walk row (degree 2; the column `trm` equals it on walk rows and is used where a
mode factor already vanishes off walk rows) -/
def trmE : Expr := sum [.mul (c wt1) (c ts1), .mul (c wt2) (c ts2), .mul (c wt3) (c ts3)]
def mDE : Expr := sub (c wk) (.add (c mS) (.add (c mK) (c mB)))
def wbE : Expr := bits (fun i => c (wb i)) 0 16
def tagE : Expr := .add (c qtb1) (.add (smul 2 (c qtb2)) (smul 3 (c qte)))
def hiE : Expr := bits (fun i => c (hb i)) 0 4
def loE : Expr := bits (fun i => c (lb i)) 0 4
def tIE : Expr := .add (c ti1) (smul 2 (c ti2))
def DE : Expr := .add (c dd1) (smul 2 (c dd2))
def sdE : Expr := .add (c sd1) (smul 2 (c sd2))
def kRD : Expr := .add (c kRDB) (c kRDE)
def kM : Expr := .add (c kMVL) (c kMVE)
/-- split cases -/
def splitE : Expr := sumc [cLSa, cLSb, cLSc, cESl0, cESl1, cESn0, cESn1]
/-- a wrapping extension exists (`I ≥ 1` in a split) -/
def pwE : Expr := .mul (.add (c ti1) (c ti2)) splitE
/-- `I ≥ 1` (a non-empty common prefix `p`) -/
def pnE : Expr := .add (c ti1) (c ti2)
/-- split branch: has a value / has the new leaf / has two windows / receives `MEMD` -/
def spValE : Expr := sumc [cLSa, cLSb, cESl0, cESl1]
def spYE : Expr := sumc [cLSa, cLSc, cESn0, cESn1]
def twoE : Expr := sumc [cLSc, cESn0, cESn1]
def spRecvE : Expr := sumc [cLSb, cLSc, cESl0, cESn0]
/-- target slot of a rewritten branch is 15 (last window) -/
def s15E : Expr := .add (.mul (c kRDB) (c sd1)) (.mul (c kRBI) (not (c ts1)))
/-- fresh 32-byte window (value digest or child digest) -/
def winFr : Expr := .add (.mul (c sVH) (not (c cp))) (.mul (c sCH) (c wfr))
def tE : Expr := bits (fun i => c (tb i)) 0 8
def cbE : Expr := bits (fun i => c (cb i)) 0 3
def ccE : Expr := bits (fun i => c (cc i)) 0 3
/-- inside-chain carry out: `cb − 3` (rows 0 … 6), the high limb `cb` (row 7) -/
def coE : Expr := .add cbE (smul 3 (sub (c fe) (k 1)))
def sigE : Expr := sub (k 1) (smul 2 (c neg))
def upbMsg (uu : Expr) : List Expr := [mid K_NPOST (c sN), c spos, c rb, c plen, sdE, uu]

/-- Kind codes of the part plan (`RD` = `RDB` or `RDE`). -/
def kindCode : Expr :=
  sum [c kRLP, smul 2 (c kRBR), smul 3 (c kRBV), smul 4 (c kRBI), smul 5 (c kMVL),
    smul 6 (c kMVE), smul 7 (c kNLF), smul 8 (c kSPB), smul 9 (c kWEX)]
/-- Planned kind code at positions 1 … 4 (bottom-up; `0` = `RD`).  `WEX` follows the
terminal parts of a split when `I ≥ 1` (`pnE·case` equals `pwE·case` under the one-hot). -/
def plan1 : Expr :=
  sum [c cLP, smul 2 (c cBR), smul 3 (c cBV), smul 7 (c cBI), smul 7 (c cLSa), smul 5 (c cLSb),
    smul 5 (c cLSc), smul 6 (c cESl0), smul 8 (c cESl1), smul 6 (c cESn0), smul 7 (c cESn1)]
def plan2 : Expr :=
  sum [smul 4 (c cBI), smul 8 (c cLSa), smul 8 (c cLSb), smul 7 (c cLSc), smul 8 (c cESl0),
    smul 9 (.mul pnE (c cESl1)), smul 7 (c cESn0), smul 8 (c cESn1)]
def plan3 : Expr :=
  sum [smul 8 (c cLSc), smul 8 (c cESn0), smul 9 (.mul pnE (sumc [cLSa, cLSb, cESl0, cESn1]))]
def plan4 : Expr := smul 9 (.mul pnE (sumc [cLSc, cESn0]))
/-- Number of terminal parts of the case. -/
def nTermE : Expr :=
  sum [c cLP, c cBR, c cBV, smul 2 (c cBI), smul 2 (c cLSa), smul 2 (c cLSb), smul 3 (c cLSc),
    smul 2 (c cESl0), c cESl1, smul 3 (c cESn0), smul 2 (c cESn1)]

/-! ## Constraints -/

/-- Booleans: row flags (everywhere), segment flags (`sf`), part flags (`pf`). -/
def rowBools : List Nat :=
  [act, wk, vb, qb, sf, wt1, wt2, wt3, pf, pl, rd, cp, aft] ++ states ++
  [fs, fe, fw, lastw, wfr, tgt, wy, wn, gD, gMs, gMr, mS, mK, mB]
def segBools : List Nat :=
  cases ++ [dd0, dd1, dd2, ts1, ts2, ts3, ti0, ti1, ti2, pres] ++ (List.range 4).map xb
def partBools : List Nat :=
  kinds ++ (List.range 4).map (fun i => jo (i + 1)) ++
  [sd0, sd1, sd2, qtl, qte, qtb1, qtb2, qodd, nokey, nochild, rootP,
   eL, eS, useA, bN, bL, cO, cS, neg, podd, vcp, xcp, spY1, spY2]

def cBool : List Expr :=
  rowBools.map (fun x => Dsl.bool (c x)) ++
  segBools.map (fun x => Expr.mul (c sf) (Dsl.bool (c x))) ++
  partBools.map (fun x => Expr.mul (c pf) (Dsl.bool (c x))) ++
  [Dsl.bool mDE] ++
  -- `reg` used as bits: nibbles on TAG/HPF rows, arithmetic on MEM rows, bitmap on W1/W2
  (List.range 8).map (fun i => Expr.mul (.add (c sTAG) (c sHPF)) (Dsl.bool (c (reg i)))) ++
  (List.range 14).map (fun i => Expr.mul (c sMEM) (Dsl.bool (c (reg i)))) ++
  (List.range 16).map (fun i => Expr.mul (.add (c wt1) (c wt2)) (Dsl.bool (c (wb i)))) ++
  [.mul (c wk) (Dsl.bool (c enter)), .mul (c wk) (Dsl.bool (c hv)),
   .mul (c wk) (Dsl.bool (c lv0)), .mul (c wk) (Dsl.bool (c lv1)), .mul (c wk) (Dsl.bool (c lv2))]

/-- Row kinds, segment and part structure. -/
def cRows : List Expr :=
  [ sub (c act) (.add (c wk) (.add (c vb) (c qb))),
    sub (c wk) (.add (c sf) (.add (c wt1) (.add (c wt2) (c wt3)))),
    .mul (c pf) (not (.add (c vb) (c qb))), .mul (c pl) (not (.add (c vb) (c qb))),
    .mul .isFirst (not (c sf)), .mul .isLast (c act),
    mul3 .isTransition (not (c act)) (n act),
    -- walk rows W0 → W1 → W2 → W3 → value part
    .mul (c sf) (not (n wt1)), .mul (c wt1) (not (n wt2)), .mul (c wt2) (not (n wt3)),
    .mul (c wt3) (not (n vb)), .mul (c wt3) (not (n pf)),
    -- value part: positions 0 … L−1, j = 0, then node part j = 1
    mul3 (c vb) (not (c pl)) (not (n vb)), mul3 (c vb) (not (c pl)) (n pf),
    mul3 (c vb) (c pl) (not (n qb)), mul3 (c vb) (c pl) (not (n pf)),
    mul3 (c vb) (c pl) (sub (.add (c qpos) (k 1)) Lexpr),
    .mul (c vb) (c j),
    mul3 (c vb) (c pl) (sub (n j) (k 1)),
    -- node parts: positions 0 … qlen−1, the part ends with its MEM field
    mul3 (c qb) (not (c pl)) (not (n qb)), mul3 (c qb) (not (c pl)) (n pf),
    .mul (mul3 (c qb) (c pl) (not (c rootP))) (not (n qb)),
    .mul (mul3 (c qb) (c pl) (not (c rootP))) (not (n pf)),
    .mul (mul3 (c qb) (c pl) (not (c rootP))) (sub (n j) (.add (c j) (k 1))),
    .mul (mul3 (c qb) (c pl) (c rootP)) (sub (n act) (n sf)),
    .mul (c qb) (sub (c pl) (.mul (c sMEM) (c fe))),
    mul3 (c qb) (c pl) (sub (.add (c qpos) (k 1)) (c qlen)),
    .mul (c qb) (.mul (c rootP) (sub (c j) (c nQ))),
    .mul (c qb) (.mul (c rootP) (sub (c qlen) (c rlen))),
    .mul (c pf) (c qpos),
    mul3 (.add (c vb) (c qb)) (not (c pl)) (sub (n qpos) (.add (c qpos) (k 1))) ]

/-- Segment constants are constant from `W0` to the end of the root part; part constants
within a part. -/
def cConst : List Expr :=
  segConst.map (fun x => Expr.mul (sub (c act) (mul3 (c qb) (c pl) (c rootP))) (sub (n x) (c x))) ++
  partConst.map (fun x => Dsl.mul3 (.add (c vb) (c qb)) (not (c pl)) (sub (n x) (c x)))

/-- The walk of `[0, 15]` (`walkV3` semantics, fixed symbols). -/
def cWalk : List Expr :=
  let stepRow := .add (c sf) (.add (c wt1) (c wt2))
  let look := .add (c mS) (.add (c mK) (c mB))
  let wrow := .add (c wt1) (.add (c wt2) (c wt3))
  [ .mul (sub (.add (c mS) (.add (c mK) (c mB))) (k 0)) (not (c wk)),
    -- W0: the head's START edge (0, τ, START, N0, 0, DOWN)
    .mul (c sf) (not (c mS)), .mul (c sf) (c nN), .mul (c sf) (sub (c nI) (c tau)),
    .mul (c sf) (c nI2), .mul (c sf) (sub (c ek) (k EK_DOWN)), .mul (c sf) (sub (c nN2) (c N0)),
    -- step: symbol, kind DOWN/KEY before W3, VAL on W3
    .mul (c mS) (sub (c nib) symE),
    .mul (mul3 (.add (c wt1) (c wt2)) (c mS) (c ek)) (sub (c ek) (k 1)),
    mul3 (c wt3) (c mS) (sub (c ek) (k EK_VAL)),
    -- a step leads to the next lookup position, which is not a drain
    mul3 stepRow (c mS) (sub (n nN) (c nN2)),
    mul3 stepRow (c mS) (sub (n nI) (c nI2)),
    mul3 stepRow (c mS) (sub (k 1) (.add (n mS) (.add (n mK) (n mB)))),
    -- after an absent terminal or a drain: drain
    mul3 (.add (c mK) (.add (c mB) mDE)) (.add (c wt1) (c wt2)) (.add (n mS) (.add (n mK) (n mB))),
    -- absent by key: a KEY or LEND edge with another symbol
    mul3 (c mK) (sub (c ek) (k EK_KEY)) (sub (c ek) (k EK_LEND)),
    .mul (c mK) (sub (.mul (sub symE (c nib)) (c inv)) (k 1)),
    -- absent at a branch: position 0; bit 0 (W1) / bit 15 (W2) clear; no value (W3)
    .mul (c mB) (c nI),
    mul3 (c wt1) (c mB) (c (wb 0)), mul3 (c wt2) (c mB) (c (wb 15)),
    mul3 (.add (c wt1) (c wt2)) (c mB) (sub (c wbm) wbE),
    mul3 (c wt3) (c mB) (c hv),
    -- levels: W1 is at N0; a step enters a new record iff it lands on position 0
    .mul (c wt1) (not (c lv0)), .mul (c wt1) (c lv1), .mul (c wt1) (c lv2),
    mul3 (.add (c wt1) (c wt2)) (c mS) (.mul (c enter) (c nI2)),
    .mul (mul3 (.add (c wt1) (c wt2)) (c mS) (not (c enter))) (sub (c nN2) (c nN)),
    mul3 (.add (c wt1) (c wt2)) (c mS) (sub (n lv0) (sub (c lv0) (.mul (c lv0) (c enter)))),
    mul3 (.add (c wt1) (c wt2)) (c mS)
      (sub (n lv1) (.add (sub (c lv1) (.mul (c lv1) (c enter))) (.mul (c lv0) (c enter)))),
    mul3 (.add (c wt1) (c wt2)) (c mS)
      (sub (n lv2) (.add (sub (c lv2) (.mul (c lv2) (c enter))) (.mul (c lv1) (c enter)))),
    -- the lookup record of a row is the path record of its level
    mul3 wrow look (sub (c nN) (sum [.mul (c lv0) (c N0), .mul (c lv1) (c N1), .mul (c lv2) (c N2)])),
    -- terminal row t*
    .mul (c wk) (sub (c trm) trmE),
    mul3 (c wt1) (.add (c ts2) (c ts3)) (not (c mS)),
    mul3 (c wt2) (c ts3) (not (c mS)),
    mul3 (c trm) (c mS) (not (c wt3)),
    .mul trmE (sub (c nI) tIE),
    .mul trmE (sub (c dd0) (c lv0)), .mul trmE (sub (c dd1) (c lv1)),
    .mul trmE (sub (c dd2) (c lv2)),
    .mul (mul3 (c trm) (c mK) (not (c cLSa))) (sub (c nib) (c tX)),
    -- case ↔ terminal
    .mul trmE (sub (c mS) (.add (c cLP) (c cBR))),
    .mul trmE (sub (c mB) (.add (c cBI) (c cBV))),
    .mul trmE (sub (c mK) splitE),
    .mul (mul3 (c trm) (c mK) (c cLSa)) (sub (c ek) (k EK_LEND)),
    .mul (mul3 (c trm) (c mK) (not (c cLSa))) (sub (c ek) (k EK_KEY)),
    -- S0F contents
    .mul (c wt3) (sub (c pres) (c mS)),
    .mul (c wt3) (sub (c vid) (.mul (c mS) (c nN2))) ]

/-- Segment-level case facts (on `W0`). -/
def cSeg : List Expr :=
  let one (xs : List Nat) := .mul (c sf) (sub (sumc xs) (k 1))
  [ one cases, one [dd0, dd1, dd2], one [ts1, ts2, ts3], one [ti0, ti1, ti2],
    -- a nibble terminal (t* ∈ {1, 2}) vs the END terminal (t* = 3)
    mul3 (c sf) (c ts3) (sumc [cBI, cLSa, cLSc, cESn0, cESn1]),
    mul3 (c sf) (.add (c ts1) (c ts2)) (sumc [cLP, cBR, cBV, cLSb, cESl0, cESl1]),
    .mul (c sf) (sub (c tX) (bits (fun i => c (xb i)) 0 4)),
    .mul (c sf) (sub (c px) (mul3 (.add (k 1) (c (xb 0))) (.add (k 1) (smul 3 (c (xb 1))))
      (.add (k 1) (smul 15 (c (xb 2)))))),
    -- split-branch bitmap: 2^x (unless LSa) + 2^y (y = 0 iff t* = 1)
    .mul (c sf) (sub (c bmL) (.add (mul3 (not (c cLSa)) (not (c (xb 3))) (c px))
      (.mul spYE (c ts1)))),
    .mul (c sf) (sub (c bmH) (.add (mul3 (not (c cLSa)) (c (xb 3)) (c px))
      (smul 128 (.mul spYE (not (c ts1)))))),
    .mul (c sf) (sub (c nQ) (.add nTermE (.add pwE DE))) ]

/-- Part plan and part headers (on the part's first row). -/
def cPlan : List Expr :=
  let g := c pf
  let gq := .mul (c qb) (c pf)
  (kinds ++ (List.range 4).map (fun i => jo (i + 1))).map (fun x => Expr.mul (c vb) (c x)) ++
  [ .mul gq (sub (sumc kinds) (k 1)),
    .mul gq (sub (sumc ((List.range 4).map fun i => jo (i + 1))) (k 1)),
    .mul gq (sub (c j) (sum ((List.range 4).map fun i => smul (i + 1) (c (jo (i + 1)))))),
    .mul g (sub kindCode (sum [.mul (c (jo 1)) plan1, .mul (c (jo 2)) plan2,
      .mul (c (jo 3)) plan3, .mul (c (jo 4)) plan4])),
    -- source record: the terminal record, or level nQ − j for a descend
    .mul gq (sub (sumc [sd0, sd1, sd2]) (k 1)),
    .mul g (sub sdE (.add (.mul (not kRD) DE) (.mul kRD (sub (c nQ) (c j))))),
    .mul g (sub (c sN) (sum [.mul (c sd0) (c N0), .mul (c sd1) (c N1), .mul (c sd2) (c N2)])),
    -- node type of Q
    .mul gq (sub (sumc [qtl, qte, qtb1, qtb2]) (k 1)),
    .mul g (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte))),
    .mul g (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2))),
    .mul g (.mul (sumc [kRDE, kMVE, kWEX]) (not (c qte))),
    .mul g (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl))),
    .mul g (.mul (c kSPB) (sub (c qtb2) spValE)),
    .mul g (.mul (c kSPB) (c nochild)),
    .mul g (.mul (c nokey) (sub (c qhk) (k 1))),
    -- fresh keys: new leaf [15] / [], wrapping extension [0] / [15] / [0, 15], moved key xs
    .mul g (.mul (c kNLF) (sub (c qhk) (k 1))), .mul g (.mul (c kNLF) (sub (c qodd) (c ts1))),
    .mul g (.mul (c kWEX) (sub (c qhk) (.add (k 1) (.mul (c ts3) (c ti2))))),
    .mul g (.mul (c kWEX) (sub (c qodd) (c ti1))),
    .mul g (.mul kM (sub (.add (smul 2 (c qhk)) (c qodd))
      (sub (.add (smul 2 (c phk)) (c podd)) (.add tIE (k 1))))),
    mul3 g (c kMVE) (.mul (c nokey) (not (c qodd))),
    -- old child taken as is: the extension key has exactly I + 1 nibbles
    .mul g (.mul (c xcp) (sub (.add (smul 2 (c phk)) (c podd)) (.add tIE (k 3)))),
    -- MEMD child: the part below (descend, wrapping extension) / the moved node (split)
    .mul g (.mul (sumc [kRDB, kRDE, kWEX]) (sub (c jm) (sub (c j) (k 1)))),
    mul3 g (c kSPB) (.mul spRecvE (sub (c jm) (k 1))),
    -- memory_usage formula
    .mul g (sub (c useA) (sum [c kRDB, c kRDE, c kRBR, c kRBV, c kRBI, c kMVE, c xcp])),
    .mul g (sub (c bN) (sum [c kRDB, c kRDE, c kWEX, .mul (c kSPB) spRecvE])),
    .mul g (sub (c bL) (c kRBR)),
    .mul g (sub (c cO) kRD),
    .mul g (sub (c cS) (c kRBR)),
    .mul g (sub (c Cc) (.mul (.add (c kMVE) (c xcp)) (.add (k 50) (smul 2 (c phk))))),
    .mul g (sub (c eL) (sum [c kRLP, c kRBV, c kRBI, c kNLF, c kSPB])),
    .mul g (sub (c eS) (.add (c kMVL) (.mul (c kSPB) (c cLSa)))),
    .mul g (sub (c Kc) (sum [
      .mul (c kRLP) (.add (k 100) (smul 2 (c qhk))), smul 50 (c kRBV), smul 102 (c kRBI),
      .mul (c kMVL) (.add (k 100) (smul 2 (c qhk))), .mul (c kMVE) (.add (k 50) (smul 2 (c qhk))),
      smul 102 (c kNLF), .mul (c kWEX) (.add (k 50) (smul 2 (c qhk))),
      .mul (c kSPB) (sum [smul 202 (c cLSa), smul 100 (sumc [cLSb, cESl0, cESl1]),
        smul 152 (sumc [cLSc, cESn0, cESn1])])])),
    -- copies: value slot, old child hash; bitmap adds of a slot insert; split-branch windows
    .mul g (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)])),
    .mul g (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1)))),
    .mul g (sub (c ba0) (.mul (c kRBI) (c ts1))),
    .mul g (sub (c ba1) (smul 128 (.mul (c kRBI) (not (c ts1))))),
    .mul g (sub (c spY1) (.mul (c kSPB) (.add (c cLSa) (.mul (c ts1) twoE)))),
    .mul g (sub (c spY2) (.mul (c kSPB) (.mul (not (c ts1)) twoE))) ]

/-- `nodeV3`'s field grammar on `Q`, windows. -/
def cFields : List Expr :=
  let inF := .mul (c qb) (not (c fe))
  let endF := mul3 (c qb) (c fe) (not (c pl))
  [ sub (sumc states) (c qb),
    .mul (c pf) (.mul (c qb) (not (c sTAG))), .mul (c pf) (.mul (c qb) (not (c fs))),
    .mul (c fs) (c idx) ] ++
  states.map (fun x => Expr.mul inF (sub (n x) (c x))) ++
  [ .mul inF (sub (n idx) (.add (c idx) (k 1))), .mul inF (n fs),
    .mul endF (n idx), .mul endF (not (n fs)),
    -- lengths
    .mul (c fe) (.mul (c sTAG) (c idx)), .mul (c fe) (.mul (c sHPL) (sub (c idx) (k 3))),
    .mul (c fe) (.mul (c sHPF) (c idx)),
    .mul (c fe) (.mul (c sKEY) (sub (.add (c idx) (k 2)) (c qhk))),
    .mul (c fe) (.mul (c sVLEN) (sub (c idx) (k 3))), .mul (c fe) (.mul (c sVH) (sub (c idx) (k 31))),
    .mul (c fe) (.mul (c sBM) (sub (c idx) (k 1))), .mul (c fe) (.mul (c sCH) (sub (c idx) (k 31))),
    .mul (c fe) (.mul (c sMEM) (sub (c idx) (k 7))),
    -- successions
    mul3 (c fe) (c sTAG) (sub (.add (c qtl) (c qte)) (n sHPL)),
    mul3 (c fe) (c sTAG) (sub (c qtb1) (n sBM)),
    mul3 (c fe) (c sTAG) (sub (c qtb2) (n sVLEN)),
    mul3 (c fe) (c sHPL) (not (n sHPF)),
    mul3 (c fe) (c sHPF) (sub (not (c nokey)) (n sKEY)),
    mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c qtl)) (n sVLEN)),
    mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c qte)) (n sCH)),
    mul3 (c fe) (c sKEY) (sub (c qtl) (n sVLEN)),
    mul3 (c fe) (c sKEY) (sub (c qte) (n sCH)),
    mul3 (c fe) (c sVLEN) (not (n sVH)),
    mul3 (c fe) (c sVH) (sub (c qtl) (n sMEM)),
    mul3 (c fe) (c sVH) (sub (c qtb2) (n sBM)),
    mul3 (c fe) (c sBM) (sub (c nochild) (n sMEM)),
    mul3 (c fe) (c sBM) (sub (not (c nochild)) (n sCH)),
    mul3 (c fe) (c sCH) (sub (k 1) (.add (n sCH) (n sMEM))),
    mul3 (c fe) (c sCH) (sub (c lastw) (n sMEM)),
    -- windows: first-window flag, window constants, extension / split-branch window counts
    mul3 (not (c sCH)) (n sCH) (not (n fw)),
    mul3 (c sCH) (not (c fe)) (sub (n fw) (c fw)),
    mul3 (c sCH) (c fe) (.mul (n sCH) (n fw)) ] ++
  [lastw, wfr, tgt, wy, wn].map (fun x => Dsl.mul3 (c sCH) (not (c fe)) (sub (n x) (c x))) ++
  [ mul3 (c qte) (c sCH) (not (c lastw)),
    .mul (mul3 (c kSPB) (c sCH) (c fw)) (sub (c lastw) (not twoE)),
    mul3 (c kSPB) (c sCH) (.mul (not (c fw)) (not (c lastw))),
    -- window roles: target window of a rewritten branch; split-branch new-leaf window
    .mul (c sCH) (sub (c tgt) (.add (.mul (c fw) (not s15E)) (.mul (c lastw) s15E))),
    mul3 (.add (c kRDB) (c kRBI)) (c sCH) (sub (c wfr) (c tgt)),
    mul3 (.add (c kRDE) (c kWEX)) (c sCH) (not (c wfr)),
    mul3 (sumc [kRBR, kRBV, kMVE]) (c sCH) (c wfr),
    mul3 (c kSPB) (c sCH) (sub (c wy) (.add (.mul (c fw) (c spY1)) (.mul (not (c fw)) (c spY2)))),
    mul3 (c kSPB) (c sCH) (sub (c wfr) (sub (k 1) (.mul (not (c wy)) (c xcp)))),
    .mul (c sCH) (sub (c wn) (.add (.mul (c kRBI) (c tgt)) (.mul (c kSPB) (c wy)))) ]

/-- Copy / read flags, bytes, read positions. -/
def cBytes : List Expr :=
  let extra := sum [
    .mul (c sTAG) (sumc [kRBV, kMVL, kMVE, xcp]),
    mul3 (c sHPL) (c fs) kM, .mul (c sHPF) kM, .mul (c sVLEN) (c kRBR),
    mul3 (c sBM) (c fs) (c xcp), .mul (c sMEM) (not (c kNLF))]
  [ .mul (not (c qb)) (c cp), .mul (not (c qb)) (c rd),
    -- which bytes are copies
    .mul (c sTAG) (sub (c cp) (sumc [kRDB, kRDE, kRLP, kRBR, kRBI])),
    .mul (.add (c sHPL) (c sHPF)) (sub (c cp) (.add (c kRDE) (c kRLP))),
    .mul (c sKEY) (sub (c cp) (sumc [kRDE, kRLP, kMVL, kMVE])),
    .mul (.add (c sVLEN) (c sVH)) (sub (c cp) (c vcp)),
    .mul (c sBM) (sub (c cp) (sumc [kRDB, kRBR, kRBV, kRBI])),
    .mul (c sCH) (sub (c cp) (not (c wfr))),
    .mul (c sMEM) (c cp),
    -- reads: copies plus header / old-value / old-memory reads
    .mul (c qb) (sub (c rd) (.add (c cp) extra)),
    -- copied bytes (a slot insert adds the new bit to the bitmap)
    .mul (c cp) (sub (c b) (.add (c rb) (.mul (c sBM) (.add (.mul (c fs) (c ba0))
      (.mul (not (c fs)) (c ba1)))))),
    -- grammar bytes: tag, hex-prefix length
    .mul (c sTAG) (sub (c b) tagE),
    mul3 (c sHPL) (c fs) (sub (c b) (c qhk)), mul3 (c sHPL) (not (c fs)) (c b),
    -- fresh hex-prefix flag bytes and the key byte of [0, 15]
    .mul (.mul (c sHPF) kM) (sub (c b) (sum [smul 32 (c qtl), smul 16 (c qodd), .mul (c qodd) loE])),
    mul3 (c sHPF) (c kNLF) (sub (c b) (.add (k 32) (smul 31 (c ts1)))),
    mul3 (c sHPF) (c kWEX) (sub (c b) (.add (smul 16 (.mul (c ts2) (c ti1))) (smul 31 (.mul (c ts3) (c ti1))))),
    mul3 (c sKEY) (c kWEX) (sub (c b) (k 15)),
    -- fresh value length (L, byte 3 = 0) and fresh windows (register)
    mul3 (c sVLEN) (not (c cp)) (sub (c b) (c (LR 0))),
    .mul winFr (sub (c b) (c (reg 0))) ] ++
  (List.range 31).map (fun i => Dsl.mul3 winFr (not (c fe)) (sub (n (reg i)) (c (reg (i + 1))))) ++
  [ -- split-branch bitmap
    mul3 (c kSPB) (c sBM) (sub (c b) (.add (.mul (c fs) (c bmL)) (.mul (not (c fs)) (c bmH)))),
    -- header reads: B_0 (TAG row: type, odd), hplen, B_e (moved key), old flags
    mul3 (.add kM (c xcp)) (c sTAG) (sub (c rb) (.add (smul 16 hiE) loE)),
    mul3 (.add kM (c xcp)) (c sTAG) (sub hiE (.add (smul 2 (c qtl)) (c podd))),
    mul3 (c sHPF) kM (sub (c rb) (.add (smul 16 hiE) loE)),
    .mul (mul3 (c sHPL) (c fs) kM) (sub (c rb) (c phk)),
    mul3 (c sBM) (c fs) (.mul (c xcp) (sub (c rb) (c phk))),
    mul3 (c kRBV) (c sTAG) (sub (c rb) (k 1)),
    mul3 (c rd) (c sVLEN) (sub (c rb) (c (SR 0))),
    -- read positions
    mul3 (c rd) (c sMEM) (sub (.add (c spos) (k 8)) (.add (c plen) (c idx))),
    mul3 (c rd) (sumc [kRDB, kRDE, kRLP, kRBR]) (sub (c spos) (c qpos)),
    mul3 (c rd) (c kRBV) (sub (.add (c spos) (smul 36 (c aft))) (c qpos)),
    mul3 (c rd) (c kRBI) (sub (.add (c spos) (smul 32 (c aft))) (c qpos)),
    mul3 (c rd) kM (.mul (c sTAG) (sub (c spos) (k 5))),
    mul3 (c rd) kM (.mul (c sHPL) (sub (c spos) (k 1))),
    mul3 (c rd) kM (.mul (sumc [sHPF, sKEY, sVLEN, sVH, sCH])
      (sub (.add (c spos) (c qhk)) (.add (c qpos) (c phk)))),
    mul3 (c rd) (c kSPB) (.mul (c sTAG) (sub (c spos) (k 5))),
    mul3 (c rd) (c kSPB) (.mul (c sBM) (sub (c spos) (k 1))),
    mul3 (c rd) (c kSPB) (.mul (.add (c sVLEN) (c sVH)) (sub (.add (c spos) (k 45)) (.add (c plen) (c qpos)))),
    mul3 (c rd) (c kSPB) (.mul (c sCH) (sub (.add (c spos) (k 40)) (.add (c plen) (c idx)))),
    -- insertion offset (RBV: after the inserted value slot; RBI: after the inserted window)
    mul3 (c kRBV) (sumc [sBM, sCH, sMEM]) (not (c aft)),
    mul3 (c kRBV) (sumc [sTAG, sVLEN, sVH]) (c aft),
    mul3 (c kRBI) (sumc [sTAG, sVLEN, sVH, sBM]) (c aft),
    mul3 (c kRBI) (c sCH) (sub (c aft) (.mul (not (c fw)) (c ts1))),
    mul3 (c kRBI) (c sMEM) (not (c aft)) ]

/-- Digest lookups: fresh windows (value / child), the new root on `W3`. -/
def cDigest : List Expr :=
  [ sub (c gD) (.add (mul3 (c qb) (c fs) winFr) (c wt3)),
    mul3 (c gD) (c sVH) (sub (c dI) (upsId (k 0))),
    mul3 (c gD) (c sVH) (sub (c dL) Lexpr),
    .mul (mul3 (c gD) (c sCH) (c wn)) (sub (c dI) (upsId (sub (c j) (k 1)))),
    .mul (mul3 (c gD) (c sCH) (c wn)) (sub (c dL) (k 50)),
    .mul (mul3 (c gD) (c sCH) (not (c wn))) (sub (c dI) (upsId (c jm))),
    .mul (mul3 (c gD) (c sCH) (not (c wn))) (sub (c dL) (c clen)),
    .mul (c wt3) (sub (c dI) (upsId (c nQ))),
    .mul (c wt3) (sub (c dL) (c rlen)) ]

/-- `memory_usage`: `R = E + max(0, A + B − C)` over the eight `MEM` rows (two carry chains;
the 9th limb is the final carry). -/
def cMem : List Expr :=
  let notLast := .mul (c sMEM) (not (c fe))
  [ .mul (c sMEM) (sub (c X1) (sub (sum [.mul (c useA) (c rb), .mul (c bN) (c mBv), .mul (c bL) (c (LR 0))])
      (sum [.mul (c cO) (c mCv), .mul (c cS) (c (SR 0)), .mul (c fs) (c Cc)]))),
    .mul (c sMEM) (sub (c Ein) (sum [.mul (c fs) (c Kc), .mul (c eL) (c (LR 0)), .mul (c eS) (c (SR 0))])),
    mul3 (c sMEM) (c fs) (c ci), mul3 (c sMEM) (c fs) (c ci2),
    .mul notLast (sub (n ci) coE), .mul notLast (sub (n ci2) ccE),
    -- inside: σ·(A + B − C) = T ≥ 0 (σ = −1 when truncated)
    .mul (c sMEM) (sub (.add (.mul sigE (c X1)) (c ci)) (.add tE (smul 256 coE))),
    -- outside: R = E + (1 − neg)·T
    .mul (c sMEM) (sub (sum [c Ein, .mul (not (c neg)) tE, c ci2]) (.add (c b) (smul 256 ccE))),
    -- exact value for the parent: byte, plus 256·(high limb) on the last row
    .mul (c sMEM) (sub (c rx) (.add (c b) (smul 256 (.mul (c fe) (.add (.mul (not (c neg)) cbE) ccE))))),
    sub (c gMs) (mul3 (c sMEM) (not (c rootP)) (not (c kNLF))),
    sub (c gMr) (.mul (c sMEM) (c bN)) ] ++
  -- L (new length) and slen (old length) registers
  (List.range 3).map (fun i => Dsl.mul3 (.add (c sVLEN) (c sMEM)) (c fs) (sub (c (LR i)) (c (Lb i)))) ++
  (List.range 2).map (fun i => Dsl.mul3 (.add (c sVLEN) (c sMEM)) (not (c fe)) (sub (n (LR i)) (c (LR (i + 1))))) ++
  [ mul3 (.add (c sVLEN) (c sMEM)) (not (c fe)) (n (LR 2)) ] ++
  (List.range 4).map (fun i => Expr.mul (c sVLEN) (sub (n (SR i)) (c (SR ((i + 1) % 4))))) ++
  (List.range 3).map (fun i => Expr.mul notLast (sub (n (SR i)) (c (SR (i + 1))))) ++
  [ .mul notLast (n (SR 3)) ] ++
  (List.range 4).map (fun i => Expr.mul (mul3 (c qb) (not (c pl)) (not (.add (c sVLEN) (c sMEM))))
    (sub (n (SR i)) (c (SR i))))

def constraints : List Expr :=
  cBool ++ cRows ++ cConst ++ cWalk ++ cSeg ++ cPlan ++ cFields ++ cBytes ++ cDigest ++ cMem

/-! ## Interactions -/

def regs : List Expr := (List.range 32).map fun i => c (reg i)
def edgeMsg (uu : Expr) : List Expr := [c nN, c nI, c nib, c nN2, c nI2, c ek, uu]
def bmapMsg (uu : Expr) : List Expr := [c nN, c wbm, c hv, uu]

def interactions : List Interaction :=
  [ recv B_MIDROOT (c sf) ([c tau] ++ regs),
    send B_ROOT (c wt3) ([.add (c tau) (k 1)] ++ regs),
    recv B_DIGEST (c gD) ([c dI, c dL] ++ regs),
    send B_S0F (c sf) [c tau, c pres, c vid],
    recv B_SPLEN (c sf) [c tau, Lexpr],
    recv B_SPOST (c vb) [c tau, c qpos, c b],
    send B_BYTES (.add (c vb) (c qb)) [upsId (c j), c qpos, c b],
    recv B_EDGE (.add (c mS) (c mK)) (edgeMsg (c u)),
    send B_EDGE (.add (c mS) (c mK)) (edgeMsg (.add (c u) (k 1))),
    recv B_BMAP (c mB) (bmapMsg (c u)),
    send B_BMAP (c mB) (bmapMsg (.add (c u) (k 1))),
    recv B_UPB (c rd) (upbMsg (c u)),
    send B_UPB (c rd) (upbMsg (.add (c u) (k 1))),
    send B_MEMD (c gMs) [c tau, c j, c idx, c rx, c rb, c qlen],
    recv B_MEMD (c gMr) [c tau, c jm, c idx, c mBv, c mCv, c clen] ]

/-- Height cap `2^22`: per instance `4 + L + Σ |Q_j|` rows (`|Q_j| ≤ 559 + 32`), with
`Σ_τ L ≤ 3,000,000` (A7) and `≤ 33` instances. -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.UpsV3
