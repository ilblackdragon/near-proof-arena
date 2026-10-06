import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Rcpt.Ids

/-!
# ZkFormal.NearV3.Rcpt.Tables.Rcpt.Layout — columns of `rcptV3`

v1's `rcpt` layout (`Near/Tables/Rcpt/Layout.lean`) with **the same indices for columns
`0 … 227`** (so that v1's extraction and render proofs transfer by adaptation), three
columns renamed for their v3 meaning, and new columns from `228`:

* `sCL` (4) is the **list-header** state: 12 rows per applied source list `j` emitting
  `u64 own ‖ u32 n_j` into `RC(j)` (v1's claim rows emitted `u64 shard ‖ u32 n` into `RC`);
* `cj` (58, v1 `rcnt`): number of receipts of the current list so far;
* `sys` (136, v1 `lo8`): the predecessor is `"system"`;
* `ee` (137, v1 `lo4`): a gas refund, `signer = receiver` (only with `sys`); it is also the
  access-key flag.

New columns:
* lists: `j`, `nj` (list index, list length), `le` (last row of a list);
* system receipts: `gq` (`ge·(1 − sys)`), `pc` (effective burn price `(1 − sys)·p`);
* signer = receiver: `gV`, `gS` (gates of `SREC` on receiver / signer rows), `sx` (received
  receiver byte), `invD`, `scnt` (count of `gS` rows), `dm`, `dd` (byte-difference mode),
  `invL` (length difference);
* access-key walk: `tB`, `symB`, `gKB` (key slot B, generalised), `fkF`, `kF`, `gF`
  (`FINAL` fields and gate), `gAK`, `uak` (`AKC` gate and use count);
* routing: `q` (interval), `eqL`, `eqH` (equal-so-far to `lo` / `hi`), `gBd` (lookup gate),
  `loB`, `hiB`, `hnB`, `uB`, `iB` (`BND` fields), `vB` (compared byte), `eL`, `eH`, `iL`, `iH`
  (equality indicators and inverses); the 9-bit differences use the scratch bits
  `xb 20 … 37`.
-/

namespace ZkFormal.NearV3.RcptV3


def act : Nat := 0
def rf : Nat := 1
def rl : Nat := 2
def lastR : Nat := 3
def sCL : Nat := 4
def sPL : Nat := 5
def sP : Nat := 6
def sVL : Nat := 7
def sV : Nat := 8
def sRID : Nat := 9
def sT0 : Nat := 10
def sSL : Nat := 11
def sS : Nat := 12
def sKT : Nat := 13
def sPK : Nat := 14
def sGP : Nat := 15
def sTL : Nat := 16
def sDEP : Nat := 17
def sXP0 : Nat := 18
def sXRI : Nat := 19
def sXG : Nat := 20
def sXST : Nat := 21
def sXL0 : Nat := 22
def sXLH : Nat := 23
def sXRH : Nat := 24
def sXRF : Nat := 25
def sXRZ : Nat := 26
def idx : Nat := 27
def fs : Nat := 28
def fe : Nat := 29
def b : Nat := 30
def e1Id : Nat := 31
def e1Pos : Nat := 32
def e1V : Nat := 33
def e1G : Nat := 34
def e2Id : Nat := 35
def e2Pos : Nat := 36
def e2V : Nat := 37
def e2G : Nat := 38
def e3Id : Nat := 39
def e3Pos : Nat := 40
def e3V : Nat := 41
def e3G : Nat := 42
def tA : Nat := 43
def symA : Nat := 44
def lastA : Nat := 45
def gKA : Nat := 46
def kz : Nat := 47
def r : Nat := 48
def o : Nat := 49
def o2 : Nat := 50
def Lp : Nat := 51
def Lv : Nat := 52
def Ls : Nat := 53
def kt : Nat := 54
def hr : Nat := 55
def kslot : Nat := 56
def tprev : Nat := 57
def cj : Nat := 58
def ge : Nat := 59
def big : Nat := 60
def oEnd : Nat := 61
def o2End : Nat := 62
def reg (i : Nat) : Nat := 63 + i
def tok (i : Nat) : Nat := 95 + i
def h2 : Nat := 111
def h3 : Nat := 112
def h5 : Nat := 113
def h6 : Nat := 114
def h7 : Nat := 115
def lb (i : Nat) : Nat := 116 + i
def z : Nat := 120
def linv : Nat := 121
def l210 : Nat := 122
def hx6 : Nat := 123
def acc : Nat := 124
def vc0 : Nat := 125
def vc1 : Nat := 126
def h01 : Nat := 127
def p1 : Nat := 128
def p2 : Nat := 129
def p3 : Nat := 130
def i1 : Nat := 131
def i2 : Nat := 132
def i3 : Nat := 133
def isys : Nat := 134
def r1 : Nat := 135
def sys : Nat := 136
def ee : Nat := 137
def xb (i : Nat) : Nat := 138 + i
def c1 : Nat := 204
def c2 : Nat := 205
def c3 : Nat := 206
def c4 : Nat := 207
def dl (i : Nat) : Nat := 208 + i
def burnt : Nat := 216
def ramt : Nat := 217
def sumD : Nat := 218
def invA : Nat := 219
def bef : Nat := 220
def lk : Nat := 221
def st : Nat := 222
def dsum : Nat := 223
def invB : Nat := 224
def dI : Nat := 225
def dL : Nat := 226
def gDg : Nat := 227

/-- The field states, in receipt order (`sCL` = list-header rows). -/
def states : List Nat := [sCL, sPL, sP, sVL, sV, sRID, sT0, sSL, sS, sKT, sPK, sGP, sTL, sDEP, sXP0, sXRI, sXG, sXST, sXL0, sXLH, sXRH, sXRF, sXRZ]



/-! ## v3 columns -/

def j : Nat := 228
def nj : Nat := 229
def le : Nat := 230
def gq : Nat := 231
def pc : Nat := 232
def gV : Nat := 233
def gS : Nat := 234
def sx : Nat := 235
def invD : Nat := 236
def scnt : Nat := 237
def dm : Nat := 238
def dd : Nat := 239
def invL : Nat := 240
def tB : Nat := 241
def symB : Nat := 242
def gKB : Nat := 243
def fkF : Nat := 244
def kF : Nat := 245
def gF : Nat := 246
def gAK : Nat := 247
def uak : Nat := 248
def q : Nat := 249
def eqL : Nat := 250
def eqH : Nat := 251
def gBd : Nat := 252
def loB : Nat := 253
def hiB : Nat := 254
def hnB : Nat := 255
def uB : Nat := 256
def iB : Nat := 257
def vB : Nat := 258
def eL : Nat := 259
def eH : Nat := 260
def iL : Nat := 261
def iH : Nat := 262
def width : Nat := 263

/-- Receipt constants (v1's, then v3's `sys ee gq dm dd q`; defined after the v3 columns). -/
def rconsts : List Nat := [r, o, o2, Lp, Lv, Ls, kt, hr, kslot, tprev, cj, ge, big, oEnd, o2End, sys, ee, gq,
  dm, dd, q]

/-- List constants (carried through the list header and the list's receipts). -/
def lconsts : List Nat := [j, nj]

end ZkFormal.NearV3.RcptV3
