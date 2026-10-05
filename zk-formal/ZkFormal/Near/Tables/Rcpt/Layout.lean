import ZkFormal.Near.Tables.Dsl

/-!
# ZkFormal.Near.Tables.Rcpt.Layout — columns of the `rcpt` table

Generated layout (see `Tables/Rcpt.lean` for the semantics):

* control `act rf rl lastR`; field states `sCL … sXRZ` (one-hot on active
  rows); `idx fs fe` (index in field, first/last row of the field); `b` (the row's byte);
* emission slots `e{1,2,3}{Id,Pos,V,G}` (`BYTES (Id, Pos, V)` with gate `G`);
* key symbols `tA symA lastA gKA` (slot A) and `kz` (the two leading 0 nibbles);
* receipt constants `r o o2 Lp Lv Ls kt hr kslot tprev rcnt ge big oEnd o2End`;
* registers `reg 0..31` (constants / digests / `bgp` / `height`, shifted one byte
  per row) and `tok 0..15` (running `tokens_burnt`);
* account-id characters: high-nibble class `h2 h3 h5 h6 h7`, low-nibble bits `lb`,
  `z linv l210 hx6`; string accumulators `acc vc0 vc1 h01 p1 p2 p3 i1 i2 i3 isys`;
* flags `r1 lo8 lo4`; scratch bits `xb 0..65`; carries-in `c1..c4`; delay line
  `dl 0..7`; arithmetic cells `burnt ramt sumD invA bef lk st dsum invB`;
  digest lookup `dI dL gDg`.
-/

namespace ZkFormal.Near.Rcpt

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
def rcnt : Nat := 58
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
def lo8 : Nat := 136
def lo4 : Nat := 137
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
def width : Nat := 228

/-- The field states, in receipt order (`sCL` = claim rows). -/
def states : List Nat := [sCL, sPL, sP, sVL, sV, sRID, sT0, sSL, sS, sKT, sPK, sGP, sTL, sDEP, sXP0, sXRI, sXG, sXST, sXL0, sXLH, sXRH, sXRF, sXRZ]

/-- Receipt constants. -/
def rconsts : List Nat := [r, o, o2, Lp, Lv, Ls, kt, hr, kslot, tprev, rcnt, ge, big, oEnd, o2End]

end ZkFormal.Near.Rcpt
