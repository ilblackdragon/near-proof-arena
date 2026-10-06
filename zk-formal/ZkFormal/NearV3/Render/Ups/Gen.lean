import ZkFormal.NearV3.Extract.Ups.View
import ZkFormal.NearV3.Extract.WalkView
import ZkFormal.Near.Render.Common

/-!
# ZkFormal.NearV3.Render.Ups.Gen — honest rows of the `upsV3` table (M7d)

Completeness side of `upsV3` (`Tables/Ups.lean`, `docs/zk-formal/UPSV3-DESIGN.md`): the
generator `test/upsv3_model.py`'s `gen`, transcribed to Lean, from a **structured instance
description** (`UpsInst`, one per `τ`).

An instance carries what the table reads and emits:
* the walk `W0 … W3` (`walk`, `WStep3`: mode, edge `[N, I, nib, N2, I2, ek]`, use count `u`,
  bitmap / `hasVal`), the path records `N`, their depths `dep`, the root record `rid`, the
  terminal facts (`D`, `ts = t*`, `ti = I`, `x`) and the case index `ci` (`UCase` order);
* the new value `v` (`L = |v|`), the pre root `mid` and the post root `post` (32 bytes each);
* the **parts** (`UpsPartI`, bottom-up, part `k` is `Q_{k+1}`): kind (`UKind` order), source
  level `sd`, record `sN`, depth `pdep`, descend counter `rc`, the part below's source `cN`,
  the source's post bytes `pb` and their `cid` column `pcid` (`UPB`), the node type `ty`
  (`0` leaf, `1` extension, `2` branch, `3` branch with value), hex-prefix lengths and
  parities `qhk qodd phk podd`, `nochild`, the field shape (`(state, length)` in `TAG … MEM`
  order `0 … 8`), the bytes `q` of `Q`, the `MEMD` child `jm` / `clen` and **the `MEMD` value**
  `mB` (the child's exact new `memory_usage`), the offset `soff` of the source's value length,
  and the sign `neg` of the `memory_usage` chain.

Cells are **integers** (`hcell`: the trace holds their images in `Fp`): the `memory_usage`
chain has negative intermediate values (`X1 = A + B − C`, carries `cb − 3`), all exact over `ℤ`.
Every derived cell is the formula of the constraint that pins it (`s15`, `tgt`, `wfr`, `cp`,
`rd`, `spos`, the part plan's selectors, …), so most constraints hold by unfolding.

Row order: per instance `W0 W1 W2 W3`, value rows `0 … L−1`, then the parts' rows; then
padding (all zero).  `UPB` use counts `u` are global (the number of earlier reads of the same
`(sN, spos)` in table order).
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Algebra

/-- One part (new node `Q_{k+1}`) of an instance. -/
structure UpsPartI where
  /-- kind index (`UKind` order: `RDB RDE RLP RBR RBV RBI MVL MVE NLF WEX SPB PT`) -/
  kind : Nat
  sd : Nat
  sN : Nat
  pdep : Nat
  rc : Nat
  cN : Nat
  /-- the source record's post bytes and `cid` column -/
  pb : List Nat
  pcid : List Nat
  /-- node type of `Q`: `0` leaf, `1` extension, `2` branch, `3` branch with value -/
  ty : Nat
  qhk : Nat
  qodd : Nat
  phk : Nat
  podd : Nat
  nochild : Nat
  /-- fields `(state, length)`, states `TAG HPL HPF KEY VLEN VH BM CH MEM` = `0 … 8` -/
  shape : List (Nat × Nat)
  /-- the bytes of `Q` -/
  q : List Nat
  jm : Nat
  clen : Nat
  /-- `MEMD` value: the child's exact new `memory_usage` -/
  mB : Nat
  /-- offset of the source's value length (`SR`) -/
  soff : Nat
  neg : Nat
  deriving Inhabited

/-- One instance `τ` of the upsert. -/
structure UpsInst where
  tau : Nat
  rid : Nat
  N : List Nat
  dep : List Nat
  walk : List WStep3
  /-- case index (`UCase` order: `LP BR BV BI LSa LSb LSc ESl0 ESl1 ESn0 ESn1`) -/
  ci : Nat
  D : Nat
  ts : Nat
  ti : Nat
  x : Nat
  v : List Nat
  mid : List Nat
  post : List Nat
  parts : List UpsPartI
  deriving Inhabited

namespace UpsGen

/-- Indicator (opaque in the proofs: a ring atom). -/
def ind (p : Prop) [Decidable p] : Int := if p then 1 else 0

/-! ## Segment constants -/

section
variable (I : UpsInst)

def L : Nat := I.v.length
def nQ : Nat := I.parts.length
def part (k : Nat) : UpsPartI := I.parts.getD k default
def rlen : Nat := (part I (nQ I - 1)).q.length
def step (t : Nat) : WStep3 := I.walk.getD t default
def wsym (t : Nat) : Nat := [SYM_START, 0, 15, SYM_END].getD t 0

/-- Bytes of `L` (`L0 L1 L2`, then `0`). -/
def Lb (i : Nat) : Int := if i = 0 then (L I % 256 : Nat) else if i = 1 then (L I / 256 % 256 : Nat)
  else if i = 2 then (L I / 65536 : Nat) else 0

def upsIdV (x : Int) : Int := 12 + 16 * (512 * (I.tau : Int) + x)
def cin (l : List Nat) : Int := (l.map fun n => ind (I.ci = n)).sum
def xbit (i : Nat) : Int := (I.x / 2 ^ i % 2 : Nat)
def pxV : Int := (2 ^ (I.x % 8) : Nat)
/-- split branch: has the new leaf / has two windows / receives `MEMD` -/
def spYc : Int := cin I [4, 6, 9, 10]
def twoC : Int := cin I [6, 9, 10]
def spRecv : Int := cin I [5, 6, 7, 9]
def bmLV : Int := (1 - cin I [4]) * (1 - xbit I 3) * pxV I + spYc I * ind (I.ts = 1)
def bmHV : Int := (1 - cin I [4]) * xbit I 3 * pxV I + 128 * (spYc I * (1 - ind (I.ts = 1)))
def presV : Int := ind ((step I 3).mode = 0)
def vidV : Int := ind ((step I 3).mode = 0) * ((step I 3).e.getD 3 0 : Nat)

/-- Segment-constant columns (`UpsV3.segConst`). -/
def isSeg (col : Nat) : Bool := (10 ≤ col && col < 49) || (176 ≤ col && col < 179) || col == 186

def segCell (col : Nat) : Int :=
  if col = 10 then I.tau
  else if col < 14 then (I.N.getD (col - 11) 0 : Nat)
  else if col < 17 then Lb I (col - 14)
  else if col < 28 then ind (I.ci = col - 17)
  else if col < 31 then ind (I.D = col - 28)
  else if col < 34 then ind (I.ts = col - 30)
  else if col < 37 then ind (I.ti = col - 34)
  else if col = 37 then I.x
  else if col < 42 then xbit I (col - 38)
  else if col = 42 then pxV I
  else if col = 43 then bmLV I
  else if col = 44 then bmHV I
  else if col = 45 then presV I
  else if col = 46 then vidV I
  else if col = 47 then nQ I
  else if col = 48 then rlen I
  else if col < 179 then (I.dep.getD (col - 176) 0 : Nat)
  else I.rid

/-! ## Walk rows `W0 … W3` -/

/-- A step enters a new record (lands on position `0`). -/
def ent (t : Nat) : Nat :=
  if (t = 1 ∨ t = 2) ∧ (step I t).mode = 0 ∧ (step I t).e.getD 4 0 = 0 then 1 else 0

/-- Level of walk row `t ≥ 1` (number of entries before it). -/
def lv (t : Nat) : Nat := (if 2 ≤ t then ent I 1 else 0) + (if 3 ≤ t then ent I 2 else 0)

def invV (t : Nat) : Int :=
  ((Fp.ofNat (wsym t) - Fp.ofNat ((step I t).e.getD 2 0))⁻¹).toNat

def wReg (t i : Nat) : Int :=
  if t = 0 then (I.mid.getD i 0 : Nat) else if t = 3 then (I.post.getD i 0 : Nat)
  else if (step I t).mode = 2 ∧ i < 16 then ((step I t).bm / 2 ^ i % 2 : Nat) else 0

def wCell (t col : Nat) : Int :=
  match col with
  | 0 => 1
  | 1 => 1
  | 4 => ind (t = 0)
  | 5 => ind (t = 1)
  | 6 => ind (t = 2)
  | 7 => ind (t = 3)
  | 49 => ((step I t).e.getD 0 0 : Nat)
  | 50 => ((step I t).e.getD 1 0 : Nat)
  | 51 => ((step I t).e.getD 2 0 : Nat)
  | 52 => ((step I t).e.getD 3 0 : Nat)
  | 53 => ((step I t).e.getD 4 0 : Nat)
  | 54 => ((step I t).e.getD 5 0 : Nat)
  | 55 => if (step I t).mode = 1 then invV I t else 0
  | 56 => if (step I t).mode = 2 then ((step I t).hv : Int) else 0
  | 57 => if (step I t).mode = 2 then ((step I t).bm : Int) else 0
  | 58 => (ent I t : Int)
  | 59 => ind (t ≠ 0 ∧ lv I t = 0)
  | 60 => ind (t ≠ 0 ∧ lv I t = 1)
  | 61 => ind (t ≠ 0 ∧ lv I t = 2)
  | 62 => ind (t ≠ 0 ∧ t = I.ts)
  | 105 => ((step I t).u : Int)
  | 124 => ind (t = 3)
  | 125 => if t = 3 then upsIdV I (nQ I) else 0
  | 126 => if t = 3 then (rlen I : Int) else 0
  | 173 => ind ((step I t).mode = 0)
  | 174 => ind ((step I t).mode = 1)
  | 175 => ind ((step I t).mode = 2)
  | col => if 129 ≤ col ∧ col < 161 then wReg I t (col - 129) else 0

/-! ## Value rows (part `j = 0`) -/

def vCell (p col : Nat) : Int :=
  match col with
  | 0 => 1
  | 2 => 1
  | 8 => ind (p = 0)
  | 9 => ind (p + 1 = L I)
  | 65 => ind (I.D = 0)
  | 66 => ind (I.D = 1)
  | 67 => ind (I.D = 2)
  | 68 => (I.N.getD I.D 0 : Nat)
  | 100 => p
  | 101 => (I.v.getD p 0 : Nat)
  | 181 => I.D
  | 182 => (I.dep.getD I.D 0 : Nat)
  | _ => 0

end

/-! ## Part constants -/

section
variable (I : UpsInst) (P : UpsPartI)

def kin (l : List Nat) : Int := (l.map fun n => ind (P.kind = n)).sum
def XcpB : Bool := P.kind == 10 && (I.ci == 8 || I.ci == 10)
def xcpV : Int := ind (XcpB I P = true)
def useAV : Int := kin P [0, 1, 3, 4, 5, 7, 11] + xcpV I P
def bNV : Int := kin P [0, 1, 9, 11] + kin P [10] * spRecv I
def bLV : Int := kin P [3]
def cOV : Int := kin P [0, 1, 11]
def cSV : Int := kin P [3]
def CcV : Int := (kin P [7] + xcpV I P) * (50 + 2 * (P.phk : Int))
def eLV : Int := kin P [2, 4, 5, 8, 10]
def eSV : Int := kin P [6] + kin P [10] * cin I [4]
def KcV : Int :=
  kin P [2] * (100 + 2 * (P.qhk : Int)) + 50 * kin P [4] + 102 * kin P [5] +
  kin P [6] * (100 + 2 * (P.qhk : Int)) + kin P [7] * (50 + 2 * (P.qhk : Int)) + 102 * kin P [8] +
  kin P [9] * (50 + 2 * (P.qhk : Int)) +
  kin P [10] * (202 * cin I [4] + 100 * cin I [5, 7, 8] + 152 * cin I [6, 9, 10])
def vcpV : Int := kin P [0, 5, 6] + kin P [10] * cin I [4]
def ba0V : Int := ind (P.kind = 5 ∧ I.ts = 1)
def ba1V : Int := 128 * ind (P.kind = 5 ∧ I.ts ≠ 1)
def Spy1B : Bool := P.kind == 10 && (I.ci == 4 || (I.ts == 1 && (I.ci == 6 || I.ci == 9 || I.ci == 10)))
def Spy2B : Bool := P.kind == 10 && I.ts != 1 && (I.ci == 6 || I.ci == 9 || I.ci == 10)
def spY1V : Int := ind (Spy1B I P = true)
def spY2V : Int := ind (Spy2B I P = true)
/-- target slot 15 (last window) -/
def S15B : Bool := (P.kind == 0 && P.sd == 1) || (P.kind == 5 && I.ts != 1)
def s15V : Int := ind (S15B I P = true)
def upV : Int := kin P [0, 1, 11]
def nokeyV : Int := ind (P.ty ≤ 1 ∧ P.qhk = 1)

/-- Part-constant columns (`UpsV3.partConst`). -/
def isPC (col : Nat) : Bool := (49 ≤ col && col < 100) || (179 ≤ col && col < 184)

def pcCell (k col : Nat) : Int :=
  if col = 49 then (k + 1 : Nat)
  else if col < 61 then ind (P.kind = col - 50)
  else if col < 65 then ind (k + 1 = col - 60)
  else if col < 68 then ind (P.sd = col - 65)
  else match col with
  | 68 => P.sN
  | 69 => P.pb.length
  | 70 => ind (P.ty = 0)
  | 71 => ind (P.ty = 1)
  | 72 => ind (P.ty = 2)
  | 73 => ind (P.ty = 3)
  | 74 => P.qhk
  | 75 => P.qodd
  | 76 => nokeyV P
  | 77 => P.nochild
  | 78 => P.q.length
  | 79 => ind (k + 1 = nQ I)
  | 80 => P.jm
  | 81 => P.clen
  | 82 => KcV I P
  | 83 => eLV P
  | 84 => eSV I P
  | 85 => useAV I P
  | 86 => bNV I P
  | 87 => bLV P
  | 88 => cOV P
  | 89 => cSV P
  | 90 => CcV I P
  | 91 => P.neg
  | 92 => P.phk
  | 93 => P.podd
  | 94 => vcpV I P
  | 95 => xcpV I P
  | 96 => ba0V I P
  | 97 => ba1V I P
  | 98 => spY1V I P
  | 99 => spY2V I P
  | 179 => ind (P.kind = 11)
  | 180 => upV P
  | 181 => P.rc
  | 182 => P.pdep
  | 183 => P.cN
  | _ => 0

end

/-! ## Node rows -/

/-- Field of byte `p`: `(state, index, field length, windows before)`; state `9` past the end. -/
def fieldAt : List (Nat × Nat) → Nat → Nat × Nat × Nat × Nat
  | [], _ => (9, 0, 0, 0)
  | (s, l) :: rest, p =>
    if p < l then (s, p, l, 0)
    else
      let r := fieldAt rest (p - l)
      (r.1, r.2.1, r.2.2.1, r.2.2.2 + if s = 7 then 1 else 0)

def nWin (sh : List (Nat × Nat)) : Nat := (sh.filter fun f => f.1 = 7).length

section
variable (I : UpsInst) (P : UpsPartI) (st ix wi : Nat)

def FwB : Bool := st == 7 && wi == 0
def LastwB : Bool := st == 7 && wi + 1 == nWin P.shape
def TgtB : Bool := st == 7 && ((FwB st wi && !S15B I P) || (LastwB P st wi && S15B I P))
def WyB : Bool := st == 7 && P.kind == 10 && ((FwB st wi && Spy1B I P) || (!FwB st wi && Spy2B I P))
def WfrB : Bool :=
  st == 7 && (((P.kind == 0 || P.kind == 5) && TgtB I P st wi) || (P.kind == 1 || P.kind == 9 || P.kind == 11) ||
    (P.kind == 10 && (WyB I P st wi || !XcpB I P)))
def WnB : Bool := st == 7 && ((P.kind == 5 && TgtB I P st wi) || (P.kind == 10 && WyB I P st wi))
def VcpB : Bool := P.kind == 0 || P.kind == 5 || P.kind == 6 || (P.kind == 10 && I.ci == 4)
/-- The byte is copied from the source. -/
def CpB : Bool :=
  (st == 0 && (P.kind == 0 || P.kind == 1 || P.kind == 2 || P.kind == 3 || P.kind == 5 || P.kind == 11)) ||
  ((st == 1 || st == 2) && (P.kind == 1 || P.kind == 2 || P.kind == 11)) ||
  (st == 3 && (P.kind == 1 || P.kind == 2 || P.kind == 6 || P.kind == 7)) ||
  ((st == 4 || st == 5) && VcpB I P) ||
  (st == 6 && (P.kind == 0 || P.kind == 3 || P.kind == 4 || P.kind == 5)) ||
  (st == 7 && !WfrB I P st wi)
/-- The row reads its target window's child id. -/
def RdcB : Bool := st == 7 && ix == 0 && TgtB I P st wi && (P.kind == 0 || P.kind == 1 || P.kind == 11)
/-- Header / old-value / old-memory reads. -/
def ExtraB : Bool :=
  (st == 0 && (P.kind == 4 || P.kind == 6 || P.kind == 7 || XcpB I P)) || (st == 1 && ix == 0 && (P.kind == 6 || P.kind == 7)) ||
  (st == 2 && (P.kind == 6 || P.kind == 7)) || (st == 4 && P.kind == 3) || (st == 6 && ix == 0 && XcpB I P) ||
  (st == 8 && P.kind != 8) || RdcB I P st ix wi
def AftB : Bool :=
  (P.kind == 4 && (st == 6 || st == 7 || st == 8)) || (P.kind == 5 && ((st == 7 && !FwB st wi && I.ts == 1) || st == 8))
def WinFrB : Bool := (st == 5 && !CpB I P st wi) || (st == 7 && WfrB I P st wi)
def GdB : Bool := ix == 0 && WinFrB I P st wi

def fwV : Int := ind (FwB st wi = true)
def lastwV : Int := ind (LastwB P st wi = true)
def tgtV : Int := ind (TgtB I P st wi = true)
def wyV : Int := ind (WyB I P st wi = true)
def wfrV : Int := ind (WfrB I P st wi = true)
def wnV : Int := ind (WnB I P st wi = true)
def cpV : Int := ind (CpB I P st wi = true)
def rdcV : Int := ind (RdcB I P st ix wi = true)
def extraV : Int := ind (ExtraB I P st ix wi = true)
def rdV : Int := ind ((CpB I P st wi || ExtraB I P st ix wi) = true)
def aftV : Int := ind (AftB I P st wi = true)

/-- Read position. -/
def sposV (p : Nat) : Int :=
  if st = 8 then (P.pb.length : Int) - 8 + ix
  else if P.kind ∈ [0, 1, 2, 3, 11] then p
  else if P.kind = 4 then (p : Int) - 36 * aftV I P st wi
  else if P.kind = 5 then (p : Int) - 32 * aftV I P st wi
  else if P.kind = 6 ∨ P.kind = 7 then
    (if st = 0 then 5 else if st = 1 then 1 else (p : Int) + P.phk - P.qhk)
  else if P.kind = 10 then
    (if st = 0 then 5 else if st = 6 then 1
      else if st = 4 ∨ st = 5 then (P.pb.length : Int) - 45 + p
      else if st = 7 then (P.pb.length : Int) - 40 + ix else 0)
  else 0

def rbV (p : Nat) : Int := (P.pb.getD (sposV I P st ix wi p).toNat 0 : Nat)

def winFrV : Int := ind (WinFrB I P st wi = true)
def gDV : Int := ind (GdB I P st ix wi = true)

/-- the digest lookup's id / length -/
def dIV (k : Nat) : Int :=
  if GdB I P st ix wi = true then
    (if st = 5 then upsIdV I 0 else if WnB I P st wi = true then upsIdV I k else upsIdV I P.jm)
  else 0
def dLV : Int :=
  if GdB I P st ix wi = true then
    (if st = 5 then (L I : Int) else if WnB I P st wi = true then 50 else P.clen)
  else 0

end

/-! ### `memory_usage` (§5) -/

section
variable (I : UpsInst) (P : UpsPartI)

/-- byte `i` of the source's `memory_usage` (its last eight bytes) -/
def memByte (Q : UpsPartI) (i : Nat) : Int := (Q.pb.getD (Q.pb.length - 8 + i) 0 : Nat)
/-- the `MEM`-row read of the source (position `plen − 8 + i`) -/
def memRb (Q : UpsPartI) (i : Nat) : Int := (Q.pb.getD (((Q.pb.length : Int) - 8 + i).toNat) 0 : Nat)
/-- byte `i` of the source's value length -/
def slb (i : Nat) : Int := if i < 4 then (P.pb.getD (P.soff + i) 0 : Nat) else 0
/-- the child part (`MEMD`) -/
def child : UpsPartI := part I (P.jm - 1)
/-- limb `i` of an exact value `R` (the high limb on row 7) -/
def limb (R : Int) (i : Nat) : Int := if i < 7 then R / 256 ^ i % 256 else R / 256 ^ 7

def Ai (i : Nat) : Int := useAV I P * memRb P i
def Bi (i : Nat) : Int := bNV I P * limb P.mB i + bLV P * Lb I i
def Ci (i : Nat) : Int :=
  cOV P * memByte (child I P) i + cSV P * slb P i + ind (i = 0) * CcV I P
def X1V (i : Nat) : Int := Ai I P i + Bi I P i - Ci I P i
def EinV (i : Nat) : Int := ind (i = 0) * KcV I P + eLV P * Lb I i + eSV I P * slb P i
def sigV : Int := 1 - 2 * (P.neg : Int)

/-- `Σ_{l < n} f l · 256^l` -/
def pfx (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => pfx f n + f n * 256 ^ n

/-- `T = σ (A + B − C)` and `R = E + (1 − neg) T` -/
def TV : Int := sigV P * pfx (X1V I P) 8
def tV (i : Nat) : Int := TV I P / 256 ^ i % 256
def RV : Int := pfx (EinV I P) 8 + (1 - (P.neg : Int)) * TV I P
/-- carries: inside chain `co`, outside chain `co2` -/
def coV (i : Nat) : Int := (sigV P * pfx (X1V I P) (i + 1) - TV I P % 256 ^ (i + 1)) / 256 ^ (i + 1)
def co2V (i : Nat) : Int :=
  (pfx (fun l => EinV I P l + (1 - (P.neg : Int)) * tV I P l) (i + 1) - RV I P % 256 ^ (i + 1)) / 256 ^ (i + 1)
def cbV (i : Nat) : Int := coV I P i + (if i < 7 then 3 else 0)

/-- `reg` on a `MEM` row `i`: `tb[8] cb[3] cc[3] ci ci2 X1 Ein` -/
def memReg (i m : Nat) : Int :=
  if m < 8 then tV I P i / 2 ^ m % 2
  else if m < 11 then cbV I P i / 2 ^ (m - 8) % 2
  else if m < 14 then co2V I P i / 2 ^ (m - 11) % 2
  else if m = 14 then (if i = 0 then 0 else coV I P (i - 1))
  else if m = 15 then (if i = 0 then 0 else co2V I P (i - 1))
  else if m = 16 then X1V I P i
  else if m = 17 then EinV I P i
  else 0

end

/-! ### Row cells -/

section
variable (I : UpsInst) (P : UpsPartI) (k p st ix fl wi u : Nat)

/-- Row cells of row `p` of part `k` (source `P`), in field `st` at index `ix` of length `fl`,
after `wi` windows. -/
def qRow (col : Nat) : Int :=
  match col with
  | 0 => 1
  | 3 => 1
  | 8 => ind (p = 0)
  | 9 => ind (p + 1 = P.q.length)
  | 100 => p
  | 101 => (P.q.getD p 0 : Nat)
  | 102 => rdV I P st ix wi
  | 103 => rbV I P st ix wi p
  | 104 => sposV I P st ix wi p
  | 105 => if (CpB I P st wi || ExtraB I P st ix wi) = true then (u : Int) else 0
  | 115 => ind (ix = 0)
  | 116 => ind (ix + 1 = fl)
  | 117 => ix
  | 118 => fwV st wi
  | 119 => lastwV P st wi
  | 120 => wfrV I P st wi
  | 121 => tgtV I P st wi
  | 122 => wyV I P st wi
  | 123 => wnV I P st wi
  | 124 => gDV I P st ix wi
  | 125 => dIV I P st ix wi k
  | 126 => dLV I P st ix wi
  | 127 => cpV I P st wi
  | 128 => aftV I P st wi
  | 168 => ind (st = 8 ∧ k + 1 ≠ nQ I ∧ P.kind ≠ 8)
  | 169 => ind (st = 8 ∧ ((P.kind = 0 ∨ P.kind = 1 ∨ P.kind = 9 ∨ P.kind = 11) ∨
      (P.kind = 10 ∧ (I.ci = 5 ∨ I.ci = 6 ∨ I.ci = 7 ∨ I.ci = 9))))
  | 170 => if st = 8 then limb (RV I P) ix else 0
  | 171 => if st = 8 then limb P.mB ix else 0
  | 172 => if st = 8 then memByte (child I P) ix else 0
  | 184 => (P.pcid.getD (sposV I P st ix wi p).toNat 0 : Nat)
  | 185 => rdcV I P st ix wi
  | col =>
    if 106 ≤ col ∧ col < 115 then ind (st = col - 106)
    else if 129 ≤ col ∧ col < 161 then
      (if winFrV I P st wi = 1 then (if col - 129 < 32 - ix then (P.q.getD (p + (col - 129)) 0 : Nat) else 0)
       else if st = 0 ∨ st = 2 then
         (if col - 129 < 4 then rbV I P st ix wi p / 16 / 2 ^ (col - 129) % 2
          else if col - 129 < 8 then rbV I P st ix wi p % 16 / 2 ^ (col - 133) % 2 else 0)
       else if st = 8 then memReg I P ix (col - 129)
       else 0)
    else if 161 ≤ col ∧ col < 164 then
      (if st = 4 ∨ st = 8 then Lb I (col - 161 + ix) else Lb I (col - 161))
    else if 164 ≤ col ∧ col < 168 then
      (if st = 4 then slb P ((col - 164 + ix) % 4)
       else if st = 8 then slb P (col - 164 + ix) else slb P (col - 164))
    else 0

end

section
variable (I : UpsInst) (k p u : Nat)

def qRowCell (col : Nat) : Int :=
  let P := part I k
  let fa := fieldAt P.shape p
  qRow I P k p fa.1 fa.2.1 fa.2.2.1 fa.2.2.2 u col

def qCell (col : Nat) : Int := if isPC col then pcCell I (part I k) k col else qRowCell I k p u col

end

/-! ## The table -/

/-- A row of an instance: walk row `t`, value row `p`, row `p` of part `k`. -/
inductive RK where
  | w (t : Nat)
  | v (p : Nat)
  | q (k p : Nat)
  deriving Inhabited, DecidableEq

def recsI (I : UpsInst) : List RK :=
  (List.range 4).map RK.w ++ (List.range (L I)).map RK.v ++
    (List.range (nQ I)).flatMap fun k => (List.range (part I k).q.length).map (RK.q k)

/-- All rows: `(instance, row)`. -/
def recs (insts : List UpsInst) : List (Nat × RK) :=
  (List.range insts.length).flatMap fun i => (recsI (insts.getD i default)).map ((i, ·))

def inst (insts : List UpsInst) (i : Nat) : UpsInst := insts.getD i default

/-- `UPB` read key of a row: `(sN, spos)`. -/
def rkey (insts : List UpsInst) : Nat × RK → Option (Nat × Int)
  | (i, .q k p) =>
    let I := inst insts i
    let P := part I k
    let fa := fieldAt P.shape p
    if (CpB I P fa.1 fa.2.2.2 || ExtraB I P fa.1 fa.2.1 fa.2.2.2) = true then some (P.sN, sposV I P fa.1 fa.2.1 fa.2.2.2 p) else none
  | _ => none

/-- `UPB` use count of row `q`: earlier reads of the same byte. -/
def uU (insts : List UpsInst) (q : Nat) : Nat :=
  (((recs insts).take q).filter fun r => rkey insts r == rkey insts ((recs insts).getD q default)).length

def rowCell (insts : List UpsInst) (q : Nat) (r : Nat × RK) (col : Nat) : Int :=
  let I := inst insts r.1
  if isSeg col then segCell I col
  else match r.2 with
    | .w t => wCell I t col
    | .v p => vCell I p col
    | .q k p => qCell I k p (uU insts q) col

/-- Number of active rows. -/
def R (insts : List UpsInst) : Nat := (recs insts).length

/-- **The cells of the honest `upsV3` table** (padding rows are zero). -/
def cell (insts : List UpsInst) (q col : Nat) : Int :=
  if q < R insts then rowCell insts q ((recs insts).getD q default) col else 0

end UpsGen

end ZkFormal.NearV3.Render
