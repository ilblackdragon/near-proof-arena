import ZkFormal.Near.Render.RcptSim
import ZkFormal.Near.Tables.Rcpt

/-!
# ZkFormal.Near.Render.Rcpt — honest rows of the `rcpt` table (closed form)

12 claim rows, one segment per receipt (fields
`PL P VL V RID T0 SL S KT PK GP TL DEP XP0 [XRI] XG XST XL0 XLH [XRH XRF XRZ]`),
then at least one padding row.  Follows `Tables/Rcpt.lean` and
`Tables/Rcpt/{Layout,Fields,Arith}.lean`: registers loaded at a field's first
row and shifted, account-id character machinery, key symbols, byte-serial gas
and balance arithmetic (carries, borrows, delay lines, bit pools in `xb`),
claim checks.  The emission slots are the table's own `emits` expressions
evaluated on the row (`fullCell`).

Closed form: the rows are the records `recsOf ds` (`RRec.cl i`: claim row `i`;
`RRec.seg r s i`: row `i` of field `s` of receipt `r`), a cell is
`fullCell ds pub bgp N ρ col`; carries and borrows are `chain`/`bchain`.  Columns and
field states are written as numerals (the indices of `Tables/Rcpt/Layout.lean`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air

namespace RcptGen

open ZkFormal.Near.Rcpt (act rf rl lastR sCL sPL sP sVL sV sRID sT0 sSL sS sKT sPK sGP sTL sDEP
  sXP0 sXRI sXG sXST sXL0 sXLH sXRH sXRF sXRZ idx fs fe b tA symA lastA gKA kz r o o2 Lp Lv Ls
  kt hr kslot tprev rcnt ge big oEnd o2End reg tok h2 h3 h5 h6 h7 lb z linv l210 hx6 acc vc0
  vc1 h01 p1 p2 p3 i1 i2 i3 isys r1 lo8 lo4 xb c1 c2 c3 c4 dl burnt ramt sumD invA bef lk st
  dsum invB dI dL gDg emits Em G_LE S_LE)

/-- Value of an expression on a row given by its cells `f` (current-row
columns, constants, public inputs; `next`/selectors read as `0` — `emits`
uses neither). -/
def evalF (f : Nat → Nat) (pub : Array Nat) : Expr → Nat
  | .const v => v % P
  | .col x false => f x % P
  | .col _ true => 0
  | .pub i => pub.getD i 0 % P
  | .isFirst | .isLast | .isTransition => 0
  | .add a d => (evalF f pub a + evalF f pub d) % P
  | .mul a d => (evalF f pub a * evalF f pub d) % P
  | .neg a => (P - evalF f pub a % P) % P

def b2n (x : Bool) : Nat := if x then 1 else 0
def bitOf (x j : Nat) : Nat := (x / 2 ^ j) % 2

/-- `Σ_{j < |g|, j ≤ i} g_j · v (i − j)` (little-endian convolution). -/
def conv (g : List Nat) (v : Nat → Nat) (i : Nat) : Nat :=
  ((List.range g.length).map fun j => if j ≤ i then g.getD j 0 * v (i - j) else 0).sum

/-- Carry into position `i` of the byte-serial sum of the values `x`. -/
def chain (x : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => (x i + chain x i) / 256

/-- Borrow into position `i` of the byte-serial `a − b` (initial borrow `b0`). -/
def bchain (a b : Nat → Nat) (b0 : Nat) : Nat → Nat
  | 0 => b0
  | i + 1 => if a i < b i + bchain a b b0 i then 1 else 0

/-- Digit `i` of the byte-serial `a − b`. -/
def bdig (a b : Nat → Nat) (b0 i : Nat) : Nat := a i + 256 * bchain a b b0 (i + 1) - b i - bchain a b b0 i

/-- `Σ_{j ≤ i} x j` -/
def runSum (x : Nat → Nat) (i : Nat) : Nat := ((List.range (i + 1)).map x).sum

/-- `(a − b)²` over the integers. -/
def sqd (a b : Nat) : Nat := (a - b) * (a - b) + (b - a) * (b - a)

def isHexC (ch : Nat) : Bool := (48 ≤ ch && ch ≤ 57) || (97 ≤ ch && ch ≤ 102)

/-- Character columns of an account-id byte. -/
def charCell (ch col : Nat) : Nat :=
  let hi := ch / 16
  let lo := ch % 16
  if col = 111 then b2n (hi == 2) else if col = 112 then b2n (hi == 3)
  else if col = 113 then b2n (hi == 5) else if col = 114 then b2n (hi == 6)
  else if col = 115 then b2n (hi == 7)
  else if col = 116 then bitOf lo 0 else if col = 117 then bitOf lo 1
  else if col = 118 then bitOf lo 2 else if col = 119 then bitOf lo 3
  else if col = 120 then b2n (lo == 0) else if col = 121 then (if lo == 0 then 0 else invP lo)
  else if col = 122 then b2n (lo % 8 == 7)
  else if col = 123 then b2n (hi == 6 && 1 ≤ lo && lo ≤ 6)
  else 0

/-- Per-receipt data. -/
structure RD where
  r : Nat
  pred : List Nat
  recv : List Nat
  id : List Nat
  signer : List Nat
  kt : Nat
  pk : List Nat
  gp : Nat
  dep : Nat
  hr : Bool
  ge : Bool
  kslot : Nat
  tprev : Nat
  bef : Nat
  locked : Nat
  stor : Nat
  big : Bool
  burnt : Nat
  ramt : Nat
  tok0 : Nat
  o : Nat
  o2 : Nat
  rcnt : Nat
  refundId : List Nat
  peoLen : Nat
  peoDig : List Nat
  deriving Inhabited

def pubs (pub : Array Nat) (off len : Nat) : List Nat := (List.range len).map fun j => pub.getD (off + j) 0

/-! ## Fields -/

/-- Length of field `s`. -/
def fLen (d : RD) (s : Nat) : Nat :=
  if s = 5 then 4 else if s = 6 then d.pred.length else if s = 7 then 4
  else if s = 8 then d.recv.length else if s = 9 then 32 else if s = 10 then 1
  else if s = 11 then 4 else if s = 12 then d.signer.length else if s = 13 then 1
  else if s = 14 then 32 + 32 * d.kt else if s = 15 then 16 else if s = 16 then 13
  else if s = 17 then 16 else if s = 18 then 4 else if s = 19 then 32 else if s = 20 then 8
  else if s = 21 then 5 else if s = 22 then 4 else if s = 23 then 32 else if s = 24 then 16
  else if s = 25 then 10 else if s = 26 then 16 else 0

/-- Register contents loaded at the first row of field `s`. -/
def fLd (d : RD) (pub : Array Nat) (s : Nat) : List Nat :=
  if s = 5 then [d.pred.length, 0, 0, 0] else if s = 6 then [115, 121, 115, 116, 101, 109]
  else if s = 7 then [d.recv.length, 0, 0, 0] else if s = 10 then [0]
  else if s = 11 then [d.signer.length, 0, 0, 0] else if s = 13 then [d.kt]
  else if s = 15 then pubs pub PV_BGP 16 else if s = 16 then [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3]
  else if s = 18 then [b2n d.hr, 0, 0, 0] else if s = 19 then d.refundId
  else if s = 20 then G_LE else if s = 21 then [2, 0, 0, 0, 0] else if s = 22 then [2, 0, 0, 0]
  else if s = 23 then d.peoDig else if s = 24 then pubs pub PV_HEIGHT 8 ++ List.replicate 8 0
  else if s = 25 then [6, 0, 0, 0, 115, 121, 115, 116, 101, 109]
  else if s = 26 then List.replicate 16 0 else []

/-- The fields of a receipt, in order. -/
def fields (h : Bool) : List Nat :=
  [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] ++ (if h then [19] else []) ++
  [20, 21, 22, 23] ++ (if h then [24, 25, 26] else [])

/-- The fields before `GP` (the tokens register holds the old total). -/
def beforeGP (s : Nat) : Bool := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14].contains s

def isStr (s : Nat) : Bool := s == 6 || s == 8 || s == 12

/-- The account-id string of field `s`. -/
def strOf (d : RD) (s : Nat) : List Nat := if s = 6 then d.pred else if s = 8 then d.recv else d.signer

/-- The byte of row `i` of field `s`. -/
def segByte (d : RD) (pub : Array Nat) (s i : Nat) : Nat :=
  if [5, 7, 11, 10, 13, 16, 18, 20, 21, 22, 24, 25, 26, 19, 23].contains s then (fLd d pub s).getD i 0
  else if isStr s then (strOf d s).getD i 0
  else if s = 9 then d.id.getD i 0
  else if s = 14 then d.pk.getD i 0
  else if s = 15 then (leBytes 16 d.gp).getD i 0
  else if s = 17 then (leBytes 16 d.dep).getD i 0
  else 0

/-! ## Gas (`GP`) and balance (`DEP`) arithmetic -/

namespace Seg
variable (d : RD) (bgp : Nat → Nat)

def gpB (i : Nat) : Nat := (leBytes 16 d.gp).getD i 0
def gbr : Nat → Nat := bchain (gpB d) bgp 0
def gdv (i : Nat) : Nat := bdig (gpB d) bgp 0 i
def pB (i : Nat) : Nat := if d.ge then bgp i else gpB d i
def surB (i : Nat) : Nat := if d.ge then gdv d bgp i else 0
def x2 : Nat → Nat := conv (G_LE.take 5) (pB d bgp)
def sb (i : Nat) : Nat := x2 d bgp i + chain (x2 d bgp) i
def x3 : Nat → Nat := conv (G_LE.take 5) (surB d bgp)
def sr (i : Nat) : Nat := x3 d bgp i + chain (x3 d bgp) i
def tokOld (i : Nat) : Nat := (leBytes 16 d.tok0).getD i 0
def tokNew (i : Nat) : Nat := (leBytes 16 (d.tok0 + d.burnt)).getD i 0
def x4 (i : Nat) : Nat := tokOld d i + sb d bgp i % 256
def tt (i : Nat) : Nat := x4 d bgp i + chain (x4 d bgp) i

def befB (i : Nat) : Nat := (leBytes 16 d.bef).getD i 0
def depB (i : Nat) : Nat := (leBytes 16 d.dep).getD i 0
def lkB (i : Nat) : Nat := (leBytes 16 d.locked).getD i 0
def stB (i : Nat) : Nat := (leBytes 8 d.stor).getD i 0
def aftB (i : Nat) : Nat := (leBytes 16 (d.bef + d.dep)).getD i 0
def totB (i : Nat) : Nat := (leBytes 16 (d.bef + d.dep + d.locked)).getD i 0
def qB (i : Nat) : Nat := (leBytes 16 (10000000000000000000 * d.stor)).getD i 0
def y1 (i : Nat) : Nat := befB d i + depB d i
def sa (i : Nat) : Nat := y1 d i + chain (y1 d) i
def y2 (i : Nat) : Nat := aftB d i + lkB d i
def stt (i : Nat) : Nat := y2 d i + chain (y2 d) i
def y3 : Nat → Nat := conv S_LE (stB d)
def sq (i : Nat) : Nat := y3 d i + chain (y3 d) i
def dbr : Nat → Nat := bchain (totB d) (qB d) 0
def ddv (i : Nat) : Nat := bdig (totB d) (qB d) 0 i
def runA (i : Nat) : Nat := runSum (fun j => 255 - aftB d j) i

end Seg

/-! ## Segment rows -/

/-- `"system"` -/
def sysB (j : Nat) : Nat := [115, 121, 115, 116, 101, 109].getD j 0

open Seg in
/-- Scratch bits `xb j` of row `i` of field `s`. -/
def segXb (d : RD) (bgp : Nat → Nat) (s i j : Nat) : Nat :=
  if s = 15 then
    if j < 8 then bitOf (gdv d bgp i) j else if j = 8 then bitOf (gbr d bgp (i + 1)) 0
    else if j < 20 then bitOf (sb d bgp i / 256) (j - 9)
    else if j < 31 then bitOf (sr d bgp i / 256) (j - 20)
    else if j < 39 then bitOf (tt d bgp i % 256) (j - 31)
    else if j = 39 then bitOf (tt d bgp i / 256) 0 else 0
  else if s = 17 then
    if j < 8 then bitOf (sa d i % 256) j else if j = 8 then bitOf (sa d i / 256) 0
    else if j < 17 then bitOf (stt d i % 256) (j - 9) else if j = 17 then bitOf (stt d i / 256) 0
    else if j < 26 then bitOf (sq d i % 256) (j - 18) else if j < 38 then bitOf (sq d i / 256) (j - 26)
    else if j < 46 then bitOf (ddv d i) (j - 38) else if j = 46 then bitOf (dbr d (i + 1)) 0
    else if j < 57 then (if i = 1 ∧ d.big = false then bitOf (770 - (stB d 0 + 256 * stB d 1)) (j - 47) else 0)
    else if j < 66 then (if i = 0 then bitOf (d.r - d.tprev) (j - 57) else 0)
    else 0
  else if isStr s ∧ i + 1 = fLen d s then
    if j < 6 then bitOf (fLen d s - 2) j else if j < 12 then bitOf (64 - fLen d s) (j - 6) else 0
  else 0

/-- Account-id accumulator `acc` (predecessor: `Σ (p_j − "system"_j)²`; receiver: hex count). -/
def accP (d : RD) (i : Nat) : Nat := runSum (fun j => sqd (d.pred.getD j 0) (sysB j)) i
def accV (d : RD) (i : Nat) : Nat := runSum (fun j => b2n (isHexC (d.recv.getD j 0))) i
def h01V (d : RD) : Nat := b2n (isHexC (d.recv.getD 0 0)) + b2n (isHexC (d.recv.getD 1 0))
def pP (d : RD) : Nat := (accP d (d.pred.length - 1) + sqd d.pred.length 6) % P
def pV1 (d : RD) : Nat := (sqd d.recv.length 64 + sqd (accV d (d.recv.length - 1)) d.recv.length) % P
def pV2 (d : RD) : Nat :=
  (sqd d.recv.length 42 + sqd (d.recv.getD 0 0) 48 + sqd (d.recv.getD 1 0) 120 +
    sqd (accV d (d.recv.length - 1)) (h01V d + 40)) % P
def pV3 (d : RD) : Nat :=
  (sqd d.recv.length 42 + sqd (d.recv.getD 0 0) 48 + sqd (d.recv.getD 1 0) 115 +
    sqd (accV d (d.recv.length - 1)) (h01V d + 40)) % P

/-- `oEnd`, `o2End` of a receipt. -/
def oEndOf (d : RD) : Nat := d.o + 123 + d.pred.length + d.recv.length + d.signer.length + 32 * d.kt
def o2EndOf (d : RD) : Nat := d.o2 + (if d.hr then 129 + 2 * d.signer.length + 32 * d.kt else 0)

/-- The tokens register of row `i` of field `s`. -/
def segTok (d : RD) (s i j : Nat) : Nat :=
  if beforeGP s then Seg.tokOld d j
  else if s = 15 then (if i + j < 16 then Seg.tokOld d (i + j) else Seg.tokNew d (i + j - 16))
  else Seg.tokNew d j

/-- Is row `i` of field `s` the receipt's last row. -/
def isRl (d : RD) (s i : Nat) : Bool := i + 1 == fLen d s && (s == 26 || (s == 23 && !d.hr))

open Seg in
/-- Cells of row `i` of field `s` of receipt `d` (`N` receipts; emission slots `0`). -/
def segCell (d : RD) (pub : Array Nat) (bgp : Nat → Nat) (N s i col : Nat) : Nat :=
  let len := fLen d s
  let bv := segByte d pub s i
  let lst := i + 1 = len
  if col < 31 then
    if col = 0 then 1 else if col = 1 then b2n (s = 5 ∧ i = 0)
    else if col = 2 then b2n (isRl d s i) else if col = 3 then b2n (isRl d s i && d.r + 1 == N)
    else if col = 27 then i else if col = 28 then b2n (i = 0) else if col = 29 then b2n lst
    else if col = 30 then bv
    else if col = 4 then 0 else if col = s then 1 else 0
  else if col < 43 then 0
  else if col < 63 then
    if col = 43 then
      (if s = 8 then 2 + 2 * i else if s = 7 ∧ i < 2 then i
       else if s = 9 ∧ i = 0 then 2 + 2 * d.recv.length else 0)
    else if col = 44 then (if s = 8 then bv / 16 else if s = 9 ∧ i = 0 then SYM_END else 0)
    else if col = 45 then b2n (s = 9 ∧ i = 0)
    else if col = 46 then b2n (s = 8 ∨ (s = 7 ∧ i < 2) ∨ (s = 9 ∧ i = 0))
    else if col = 47 then b2n (s = 7 ∧ i < 2)
    else if col = 48 then d.r else if col = 49 then d.o else if col = 50 then d.o2
    else if col = 51 then d.pred.length else if col = 52 then d.recv.length
    else if col = 53 then d.signer.length else if col = 54 then d.kt else if col = 55 then b2n d.hr
    else if col = 56 then d.kslot else if col = 57 then d.tprev else if col = 58 then d.rcnt
    else if col = 59 then b2n d.ge else if col = 60 then b2n d.big
    else if col = 61 then oEndOf d else if col = 62 then o2EndOf d else 0
  else if col < 95 then (fLd d pub s).getD (i + (col - 63)) 0
  else if col < 111 then segTok d s i (col - 95)
  else if col < 124 then (if isStr s then charCell bv col else 0)
  else if col < 138 then
    if col = 124 then (if s = 6 then accP d i % P else if s = 8 then accV d i else 0)
    else if col = 125 then (if s = 8 then d.recv.getD 0 0 else 0)
    else if col = 126 then (if s = 8 then d.recv.getD 1 0 else 0)
    else if col = 127 then (if s = 8 then h01V d else 0)
    else if col = 128 then (if s = 6 ∧ lst then pP d else if s = 8 ∧ lst then pV1 d else 0)
    else if col = 129 then (if s = 8 ∧ lst then pV2 d else 0)
    else if col = 130 then (if s = 8 ∧ lst then pV3 d else 0)
    else if col = 131 then (if s = 8 ∧ lst then invP (pV1 d) else 0)
    else if col = 132 then (if s = 8 ∧ lst then invP (pV2 d) else 0)
    else if col = 133 then (if s = 8 ∧ lst then invP (pV3 d) else 0)
    else if col = 134 then (if s = 6 ∧ lst then invP (pP d) else 0)
    else if col = 135 then b2n (s = 17 ∧ i = 1)
    else 0
  else if col < 204 then segXb d bgp s i (col - 138)
  else if s = 15 then
    if col = 204 then gbr d bgp i else if col = 205 then chain (x2 d bgp) i
    else if col = 206 then chain (x3 d bgp) i else if col = 207 then chain (x4 d bgp) i
    else if col < 212 then (if col - 208 < i then pB d bgp (i - 1 - (col - 208)) else 0)
    else if col < 216 then (if col - 212 < i then surB d bgp (i - 1 - (col - 212)) else 0)
    else if col = 216 then sb d bgp i % 256 else if col = 217 then sr d bgp i % 256
    else if col = 218 then runSum (gdv d bgp) i
    else if col = 219 then (if lst ∧ d.hr then invP (runSum (gdv d bgp) i) else 0)
    else 0
  else if s = 17 then
    if col = 204 then chain (y1 d) i else if col = 205 then chain (y2 d) i
    else if col = 206 then chain (y3 d) i else if col = 207 then dbr d i
    else if col < 215 then (if col - 208 < i then stB d (i - 1 - (col - 208)) else 0)
    else if col = 220 then befB d i else if col = 221 then lkB d i else if col = 222 then stB d i
    else if col = 223 then runA d i else if col = 224 then (if lst then invP (runA d i) else 0)
    else 0
  else if col = 227 then b2n (i = 0 ∧ (s = 19 ∨ s = 23))
  else if col = 225 then
    (if i = 0 ∧ s = 19 then msgId K_RID d.r else if i = 0 ∧ s = 23 then msgId K_PEO d.r else 0)
  else if col = 226 then (if i = 0 ∧ s = 19 then 48 else if i = 0 ∧ s = 23 then d.peoLen else 0)
  else 0

/-! ## Claim rows -/

namespace Cl
variable (pub : Array Nat)

def A : List Nat := pubs pub PV_SHARD 8 ++ pubs pub PV_N 4
def B : List Nat := pubs pub PV_NREF 4
def D : List Nat := pubs pub PV_GASLIM 8
def T : List Nat := pubs pub PV_GAS 8
def n : Nat := (pubs pub PV_N 4).foldr (fun x a => x + 256 * a) 0
def yB : List Nat := leBytes 8 ((n pub - 1) * Params.G)
def x1 (i : Nat) : Nat := (n pub - 1) * G_LE.getD i 0
def sy (i : Nat) : Nat := x1 pub i + chain (x1 pub) i
def br : Nat → Nat := bchain (fun i => (D pub).getD i 0) (fun i => (yB pub).getD i 0) 1
def dv (i : Nat) : Nat := bdig (fun i => (D pub).getD i 0) (fun i => (yB pub).getD i 0) 1 i
def x3 (i : Nat) : Nat := (yB pub).getD i 0 + G_LE.getD i 0
def sg (i : Nat) : Nat := x3 pub i + chain (x3 pub) i

end Cl

open Cl in
/-- Cells of claim row `i`. -/
def clCell (pub : Array Nat) (i col : Nat) : Nat :=
  if col = 0 then 1 else if col = 4 then 1 else if col = 27 then i
  else if col = 28 then b2n (i = 0) else if col = 29 then b2n (i = 11)
  else if 63 ≤ col ∧ col < 75 then (A pub).getD ((i + (col - 63)) % 12) 0
  else if 75 ≤ col ∧ col < 79 then (B pub).getD ((i + (col - 75)) % 4) 0
  else if 79 ≤ col ∧ col < 87 then G_LE.getD ((i + (col - 79)) % 8) 0
  else if 87 ≤ col ∧ col < 95 then (D pub).getD ((i + (col - 87)) % 8) 0
  else if 95 ≤ col ∧ col < 103 then (T pub).getD ((i + (col - 95)) % 8) 0
  else if col = 136 then b2n (i < 8) else if col = 137 then b2n (i < 4)
  else if col = 219 then (if i = 0 then invP (pub.getD PV_N 0 + pub.getD (PV_N + 1) 0) else 0)
  else if i < 8 then
    if col = 204 then chain (x1 pub) i else if col = 205 then br pub i else if col = 206 then chain (x3 pub) i
    else if 138 ≤ col ∧ col < 146 then bitOf (sy pub i % 256) (col - 138)
    else if 146 ≤ col ∧ col < 154 then bitOf (sy pub i / 256) (col - 146)
    else if 154 ≤ col ∧ col < 162 then bitOf (dv pub i) (col - 154)
    else if col = 162 then bitOf (br pub (i + 1)) 0
    else if col = 163 then bitOf (sg pub i / 256) 0
    else 0
  else 0

/-! ## Rows -/

/-- Row records: claim row `i`; row `i` of field `s` of receipt `r`. -/
inductive RRec
  | cl (i : Nat)
  | seg (r s i : Nat)
  deriving Inhabited, DecidableEq

def stateOf : RRec → Nat
  | .cl _ => sCL
  | .seg _ s _ => s

/-- The emissions of state `s`. -/
def emitsOf (s : Nat) : List Em := ((emits.find? (·.1 == s)).map (·.2)).getD []

def emSel (em : Em) : Nat → Expr
  | 0 => em.1
  | 1 => em.2.1
  | 2 => em.2.2.1
  | _ => em.2.2.2

/-- Cells of a row, emission slots `0`. -/
def baseCell (ds : Array RD) (pub : Array Nat) (bgp : Nat → Nat) (N : Nat) : RRec → Nat → Nat
  | .cl i, col => clCell pub i col
  | .seg r s i, col => segCell (ds.getD r default) pub bgp N s i col

/-- Cells of a row (emission slots `31 … 42` from `emits`). -/
def fullCell (ds : Array RD) (pub : Array Nat) (bgp : Nat → Nat) (N : Nat) (ρ : RRec) (col : Nat) : Nat :=
  if 31 ≤ col ∧ col < 43 then
    match (emitsOf (stateOf ρ))[(col - 31) / 4]? with
    | some em => evalF (baseCell ds pub bgp N ρ) pub (emSel em ((col - 31) % 4))
    | none => 0
  else baseCell ds pub bgp N ρ col

/-- The rows of one receipt. -/
def segRecs (d : RD) : List RRec :=
  (fields d.hr).flatMap fun s => (List.range (fLen d s)).map (RRec.seg d.r s)

/-- All active rows. -/
def recsOf (ds : List RD) : List RRec := (List.range 12).map RRec.cl ++ ds.flatMap segRecs

end RcptGen

open RcptGen in
/-- Data of receipt `r` (`o`, `o2`, `rcnt`: prefix sums over the earlier receipts). -/
def rdOf (I : Info) (r : Nat) : RcptGen.RD :=
  let e := I.e
  let c := I.c
  let rc := e.rc r
  let k := e.slot r
  let a0 := e.acc0 k
  let bef := e.amtAt k r
  let aft := bef + rc.deposit
  let hr := hasRefund I r
  let rfLen (r' : Nat) : Nat := if hasRefund I r' then
    (toNats (gasRefundReceipt (e.rc r') c.blockHeight (surplusOf c.blockGasPrice (e.rc r'))).encode).length else 0
  { r, pred := toNats rc.predecessorId, recv := toNats rc.receiverId, id := toNats rc.receiptId,
    signer := toNats rc.signerId, kt := rc.signerPk.tag, pk := toNats rc.signerPk.data,
    gp := rc.gasPrice, dep := rc.deposit, hr, ge := c.blockGasPrice ≤ rc.gasPrice,
    kslot := k, tprev := tprevOf e r, bef, locked := a0.locked, stor := a0.storageUsage,
    big := 10000000000000000000 * a0.storageUsage ≤ aft + a0.locked,
    burnt := burntOf c.blockGasPrice rc, ramt := surplusOf c.blockGasPrice rc,
    tok0 := e.tokAt c r,
    o := 12 + ((List.range r).map fun r' => (toNats (e.rc r').encode).length).sum,
    o2 := 4 + ((List.range r).map rfLen).sum,
    rcnt := ((List.range r).map fun r' => b2n (hasRefund I r')).sum,
    refundId := shaN (ridBytes I r), peoLen := (peoBytes I r).length,
    peoDig := shaN (peoBytes I r) }

/-- Per-receipt data from the records. -/
def rcptData (I : Info) : List RcptGen.RD := (List.range I.nRcpt).map (rdOf I)

/-- The claim as public-input naturals. -/
def pubArr (I : Info) : Array Nat := (toNats I.c.encode).toArray

/-- Cell `(q, col)` of the honest `rcpt` table (`0` on padding rows). -/
def rcptCell (pub : Array Nat) (bgp : Nat → Nat) (N : Nat) (R : Array RcptGen.RRec) (ds : Array RcptGen.RD)
    (q col : Nat) : Nat :=
  if q < R.size then RcptGen.fullCell ds pub bgp N (R.getD q (.cl 0)) col else 0

/-- Honest rows of the `rcpt` table (padded, at least one padding row). -/
def rcptRowsAll (I : Info) : Array Row :=
  let pub := pubArr I
  let bgpL := leBytes 16 I.c.blockGasPrice
  let ds := (rcptData I).toArray
  let R := (RcptGen.recsOf (rcptData I)).toArray
  mkTab (2 ^ logOf (R.size + 1)) Rcpt.width (rcptCell pub (fun i => bgpL.getD i 0) I.nRcpt R ds)

end ZkFormal.Near.Render
