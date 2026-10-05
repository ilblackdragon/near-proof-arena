import ZkFormal.Near.Tables.Rcpt.Fields
import ZkFormal.Near.Ids

/-!
# ZkFormal.Near.Tables.Rcpt.Arith — registers, account ids, gas, balances, claim checks

* **Registers.** `reg` is loaded at a field's first row (constants, `bgp`,
  `height`, `"system"`, or a digest) and shifted one byte per row, so the
  row's byte is `reg 0`.  `tok` holds `tokens_burnt` and is rewritten byte by
  byte in the `GP` rows.
* **Account ids** (`P`, `V`, `S`): every byte is `16·hi + lo` with the high
  nibble one-hot over `{2,3,5,6,7}` and the low nibble in bits; the character
  classes of `AccountId.valid` (alnum / separator, no leading, trailing or
  doubled separator, length `2..64`), `predecessor ≠ "system"` and a named
  receiver (not 64-hex, not `0x`/`0s` + 40 hex) by running sums and inverses.
* **Gas** (`GP`, LSB first): `gp − bgp` with borrow (`ge` = `gp ≥ bgp`), `p`,
  surplus, `burnt = G·p`, `ramt = G·surplus` (no overflow), running tokens.
* **Balances** (`DEP`): `aft = bef + deposit < 2^128`, `aft ≠ u128::MAX`,
  `tot = aft + locked < 2^128`, `q = 10^19·storage`, `tot ≥ q` or
  `storage ≤ 770`; `r − tprev < 2^9`.
* **Claim** (`CL`, 12 rows): the fixed claim prefix, `1 ≤ n ≤ 256`,
  `(n − 1)·G < gasLimit`, `gasBurnt = n·G`; the `RC`/`RF` headers.
* **End** (`lastR`): `n` receipts, refund count, tokens.
-/

namespace ZkFormal.Near.Rcpt

open ZkFormal.Air ZkFormal.Near.Dsl NearSpec

def bitsX (off len : Nat) : Expr := bits (fun j => c (xb j)) off len
def bitsXn (off len : Nat) : Expr := bits (fun j => n (xb j)) off len
def pubs (off len : Nat) : List Expr := (List.range len).map fun j => .pub (off + j)
def ks (l : List Nat) : List Expr := l.map k
def leE (l : List Expr) : Expr := sum ((l.zip (List.range l.length)).map fun (e, j) => smul (256 ^ j) e)

def G_LE : List Nat := [196, 164, 183, 246, 51, 0, 0, 0]
def S_LE : List Nat := [0, 0, 232, 137, 4, 35, 199, 138]
def nPubE : Expr := leE (pubs PV_N 4)
def nrefPubE : Expr := leE (pubs PV_NREF 4)

/-! ## Registers -/

/-- `(state, register contents loaded at the field's first row)` -/
def loads : List (Nat × List Expr) :=
  [ (sPL, [c Lp, k 0, k 0, k 0]), (sVL, [c Lv, k 0, k 0, k 0]), (sSL, [c Ls, k 0, k 0, k 0]),
    (sT0, [k 0]), (sKT, [c kt]), (sTL, ks [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3]),
    (sXP0, [c hr, k 0, k 0, k 0]), (sXG, ks G_LE), (sXST, ks [2, 0, 0, 0, 0]),
    (sXL0, ks [2, 0, 0, 0]), (sXRH, pubs PV_HEIGHT 8 ++ ks (List.replicate 8 0)),
    (sXRF, ks [6, 0, 0, 0, 115, 121, 115, 116, 101, 109]), (sXRZ, ks (List.replicate 16 0)),
    (sP, ks [115, 121, 115, 116, 101, 109]), (sGP, pubs PV_BGP 16) ]

/-- States whose byte is the register head. -/
def regStates : List Nat :=
  [sPL, sVL, sSL, sT0, sKT, sTL, sXP0, sXG, sXST, sXL0, sXRH, sXRF, sXRZ, sXRI, sXLH]

/-- Claim-row register blocks `(first column, length)`, rotated cyclically. -/
def clBlocks : List (Nat → Nat) × List Nat :=
  ([fun j => reg j, fun j => reg (12 + j), fun j => reg (16 + j), fun j => reg (24 + j),
    fun j => tok j], [12, 4, 8, 8, 8])

def rot (col : Nat → Nat) (len : Nat) : List Expr :=
  (List.range len).map fun j => mul3 (c sCL) (not (c fe)) (sub (n (col j)) (c (col ((j + 1) % len))))

def cRegs : List Expr :=
  loads.flatMap (fun (s, l) =>
    (l.zip (List.range l.length)).map fun (e, j) => mul3 (c s) (c fs) (sub (c (reg j)) e)) ++
  [ .mul (sum (regStates.map c)) (sub (c b) (c (reg 0))) ] ++
  (List.range 31).map (fun j => mul3 rowE (not (c fe)) (sub (n (reg j)) (c (reg (j + 1))))) ++
  -- claim rows: loads on the first row, cyclic rotations
  ((pubs PV_SHARD 8 ++ pubs PV_N 4 ++ pubs PV_NREF 4 ++ ks G_LE ++ pubs PV_GASLIM 8).zip
      (List.range 32)).map (fun (e, j) => .mul .isFirst (sub (c (reg j)) e)) ++
  ((pubs PV_GAS 8 ++ ks (List.replicate 8 0)).zip (List.range 16)).map
      (fun (e, j) => .mul .isFirst (sub (c (tok j)) e)) ++
  rot (fun j => reg j) 12 ++ rot (fun j => reg (12 + j)) 4 ++ rot (fun j => reg (16 + j)) 8 ++
  rot (fun j => reg (24 + j)) 8 ++ rot (fun j => tok j) 8 ++
  -- tokens: zero before the first receipt, rewritten in GP rows, kept otherwise
  (List.range 16).map (fun j => mul3 (c sCL) (c fe) (n (tok j))) ++
  (List.range 15).map (fun j => .mul (c sGP) (sub (n (tok j)) (c (tok (j + 1))))) ++
  [ .mul (c sGP) (sub (n (tok 15)) (bitsX 31 8)) ] ++
  (List.range 16).map (fun j => .mul (sub (sub rowE (c sGP)) (c lastR)) (sub (n (tok j)) (c (tok j))))

/-! ## Account ids -/

def SS : Expr := sum [c sP, c sV, c sS]
def hiE : Expr := sum [smul 2 (c h2), smul 3 (c h3), smul 5 (c h5), smul 6 (c h6), smul 7 (c h7)]
def loE : Expr := bits (fun j => c (lb j)) 0 4
def sepE : Expr := .add (c h2) (c h5)
def sepN : Expr := .add (n h2) (n h5)
def hexE : Expr := .add (c h3) (c hx6)
def hexN : Expr := .add (n h3) (n hx6)
def sq (e : Expr) : Expr := .mul e e
def lb' (j : Nat) : Expr := c (lb j)

def cChars : List Expr :=
  ([h2, h3, h5, h6, h7, z, hx6] ++ (List.range 4).map lb).map (fun x => bool (c x)) ++
  [ .mul SS (sub (c b) (.add (smul 16 hiE) loE)),
    .mul SS (sub (sum [c h2, c h3, c h5, c h6, c h7]) (k 1)),
    -- low nibble ranges per high nibble
    mul3 (c h3) (lb' 3) (lb' 2), mul3 (c h3) (lb' 3) (lb' 1),
    .mul (c z) loE, mul3 SS (not (c z)) (sub (.mul loE (c linv)) (k 1)),
    .mul (c h6) (c z),
    mul3 (c h7) (lb' 3) (lb' 2), .mul (mul3 (c h7) (lb' 3) (lb' 1)) (lb' 0),
    .mul (c h2) (not (lb' 3)), .mul (c h2) (not (lb' 2)), .mul (c h2) (sub (.add (lb' 1) (lb' 0)) (k 1)),
    .mul (c h5) (not (lb' 0)), .mul (c h5) (not (lb' 1)), .mul (c h5) (not (lb' 2)),
    .mul (c h5) (not (lb' 3)),
    -- hex letters a–f
    sub (c l210) (mul3 (lb' 2) (lb' 1) (lb' 0)),
    .mul (c hx6) (not (c h6)), .mul (c hx6) (lb' 3), .mul (c hx6) (c l210),
    mul3 (sub (c h6) (c hx6)) (not (lb' 3)) (not (c l210)),
    -- separators: not first, not last, never doubled
    .mul (mul3 SS (not (c fe)) sepE) sepN, mul3 SS (c fs) sepE, mul3 SS (c fe) sepE,
    -- lengths 2..64
    mul3 (c fe) (c sP) (sub (sub (c Lp) (k 2)) (bitsX 0 6)),
    mul3 (c fe) (c sV) (sub (sub (c Lv) (k 2)) (bitsX 0 6)),
    mul3 (c fe) (c sS) (sub (sub (c Ls) (k 2)) (bitsX 0 6)),
    -- predecessor ≠ "system"
    mul3 (c sP) (c fs) (sub (c acc) (sq (sub (c b) (c (reg 0))))),
    mul3 (c sP) (not (c fe)) (sub (n acc) (.add (c acc) (sq (sub (n b) (n (reg 0)))))),
    mul3 (c sP) (c fe) (sub (c p1) (.add (c acc) (sq (sub (c Lp) (k 6))))),
    mul3 (c sP) (c fe) (sub (.mul (c p1) (c isys)) (k 1)),
    -- named receiver
    mul3 (c sV) (c fs) (sub (c acc) hexE),
    mul3 (c sV) (not (c fe)) (sub (n acc) (.add (c acc) hexN)),
    mul3 (c sV) (c fs) (sub (c vc0) (c b)), mul3 (c sV) (c fs) (sub (c vc1) (n b)),
    mul3 (c sV) (c fs) (sub (c h01) (.add hexE hexN)),
    mul3 (c sV) (not (c fe)) (sub (n vc0) (c vc0)), mul3 (c sV) (not (c fe)) (sub (n vc1) (c vc1)),
    mul3 (c sV) (not (c fe)) (sub (n h01) (c h01)),
    mul3 (c sV) (c fe) (sub (c p1) (.add (sq (sub (c Lv) (k 64))) (sq (sub (c acc) (c Lv))))),
    mul3 (c sV) (c fe) (sub (c p2) (sum [sq (sub (c Lv) (k 42)), sq (sub (c vc0) (k 48)),
      sq (sub (c vc1) (k 120)), sq (sub (sub (c acc) (c h01)) (k 40))])),
    mul3 (c sV) (c fe) (sub (c p3) (sum [sq (sub (c Lv) (k 42)), sq (sub (c vc0) (k 48)),
      sq (sub (c vc1) (k 115)), sq (sub (sub (c acc) (c h01)) (k 40))])),
    mul3 (c sV) (c fe) (sub (.mul (c p1) (c i1)) (k 1)),
    mul3 (c sV) (c fe) (sub (.mul (c p2) (c i2)) (k 1)),
    mul3 (c sV) (c fe) (sub (.mul (c p3) (c i3)) (k 1)) ]

/-! ## Key symbols (slot A; slot B is the low nibble of a receiver character) -/

def cKey : List Expr :=
  [ sub (c gKA) (sum [c sV, c kz, .mul (c sRID) (c fs)]),
    .mul (c sV) (sub (c tA) (.add (k 2) (smul 2 (c idx)))), .mul (c sV) (sub (c symA) hiE),
    .mul (c sV) (c lastA),
    .mul (c kz) (sub (c tA) (c idx)), .mul (c kz) (c symA), .mul (c kz) (c lastA),
    mul3 (c sRID) (c fs) (sub (c tA) (.add (k 2) (smul 2 (c Lv)))),
    mul3 (c sRID) (c fs) (sub (c symA) (k SYM_END)),
    mul3 (c sRID) (c fs) (sub (c lastA) (k 1)),
    .mul (c kz) (not (c sVL)), mul3 (c sVL) (c fs) (not (c kz)),
    mul3 (c sVL) (not (c fe)) (sub (n kz) (c fs)) ]

/-! ## Gas (`GP` rows) -/

def DE : Expr := bitsX 0 8
def DEn : Expr := bitsXn 0 8
def pE : Expr := .add (.mul (c ge) (c (reg 0))) (.mul (not (c ge)) (c b))
def surE : Expr := .mul (c ge) DE
def conv (cs : List Nat) (x : Expr) (dl : Nat → Expr) : Expr :=
  sum ((cs.zip (List.range cs.length)).map fun (g, j) => smul g (if j = 0 then x else dl (j - 1)))
/-- bytes `16..` of `G·x` from the last row (`x`, `dl 0..2`): must vanish -/
def ovf (x : Expr) (dl : Nat → Expr) : Expr :=
  sum [smul (164 + 183 + 246 + 51) x, smul (183 + 246 + 51) (dl 0), smul (246 + 51) (dl 1),
       smul 51 (dl 2)]

def gp : Expr := c sGP
def cGas : List Expr :=
  let d (j : Nat) : Expr := c (dl j)
  [ .mul gp (sub (sub (c b) (c (reg 0))) (sub (.add (c c1) DE) (smul 256 (c (xb 8))))),
    .mul (.mul gp (c fs)) (c c1), mul3 gp (not (c fe)) (sub (n c1) (c (xb 8))),
    mul3 gp (c fe) (sub (c (xb 8)) (not (c ge))),
    -- burnt = G·p
    .mul gp (sub (.add (c burnt) (smul 256 (bitsX 9 11))) (.add (conv (G_LE.take 5) pE d) (c c2))),
    .mul (.mul gp (c fs)) (c c2), mul3 gp (not (c fe)) (sub (n c2) (bitsX 9 11)),
    mul3 gp (c fe) (bitsX 9 11), mul3 gp (c fe) (ovf pE d),
    -- refund amount = G·surplus
    .mul gp (sub (.add (c ramt) (smul 256 (bitsX 20 11)))
      (.add (conv (G_LE.take 5) surE (fun j => d (4 + j))) (c c3))),
    .mul (.mul gp (c fs)) (c c3), mul3 gp (not (c fe)) (sub (n c3) (bitsX 20 11)),
    mul3 gp (c fe) (bitsX 20 11), mul3 gp (c fe) (ovf surE (fun j => d (4 + j))),
    -- running tokens
    .mul gp (sub (.add (bitsX 31 8) (smul 256 (c (xb 39)))) (sum [c (tok 0), c burnt, c c4])),
    .mul (.mul gp (c fs)) (c c4), mul3 gp (not (c fe)) (sub (n c4) (c (xb 39))),
    mul3 gp (c fe) (c (xb 39)),
    -- refund flag: surplus bytes vanish without a refund; a refund has a nonzero surplus
    .mul (mul3 gp (not (c hr)) (c ge)) DE,
    mul3 gp (c fs) (sub (c sumD) DE),
    mul3 gp (not (c fe)) (sub (n sumD) (.add (c sumD) DEn)),
    mul3 gp (c fe) (sub (.mul (c sumD) (c invA)) (c hr)) ] ++
  -- delay lines of p and surplus
  (List.range 8).map (fun j => mul3 gp (c fs) (d j)) ++
  [ mul3 gp (not (c fe)) (sub (n (dl 0)) pE), mul3 gp (not (c fe)) (sub (n (dl 4)) surE) ] ++
  ([1, 2, 3, 5, 6, 7].map fun j => mul3 gp (not (c fe)) (sub (n (dl j)) (d (j - 1))))

/-! ## Balances (`DEP` rows) -/

def dp : Expr := c sDEP
def aftE : Expr := bitsX 0 8
def cDep : List Expr :=
  let d (j : Nat) : Expr := c (dl j)
  [ .mul dp (sub (sum [c bef, c b, c c1]) (.add aftE (smul 256 (c (xb 8))))),
    .mul (.mul dp (c fs)) (c c1), mul3 dp (not (c fe)) (sub (n c1) (c (xb 8))),
    mul3 dp (c fe) (c (xb 8)),
    -- amount ≠ u128::MAX
    mul3 dp (c fs) (sub (c dsum) (sub (k 255) aftE)),
    mul3 dp (not (c fe)) (sub (n dsum) (.add (c dsum) (sub (k 255) (bitsXn 0 8)))),
    mul3 dp (c fe) (sub (.mul (c dsum) (c invB)) (k 1)),
    -- tot = aft + locked < 2^128
    .mul dp (sub (sum [aftE, c lk, c c2]) (.add (bitsX 9 8) (smul 256 (c (xb 17))))),
    .mul (.mul dp (c fs)) (c c2), mul3 dp (not (c fe)) (sub (n c2) (c (xb 17))),
    mul3 dp (c fe) (c (xb 17)),
    -- q = 10^19·storage
    .mul dp (sub (.add (conv S_LE (c st) d) (c c3)) (.add (bitsX 18 8) (smul 256 (bitsX 26 12)))),
    .mul (.mul dp (c fs)) (c c3), mul3 dp (not (c fe)) (sub (n c3) (bitsX 26 12)),
    mul3 dp (c fe) (bitsX 26 12),
    mul3 dp (not (c fe)) (sub (n (dl 0)) (c st)),
    -- tot − q with borrow; no final borrow when `big`
    .mul dp (sub (sub (bitsX 9 8) (bitsX 18 8)) (sub (.add (c c4) (bitsX 38 8)) (smul 256 (c (xb 46))))),
    .mul (.mul dp (c fs)) (c c4), mul3 dp (not (c fe)) (sub (n c4) (c (xb 46))),
    .mul (mul3 dp (c fe) (c big)) (c (xb 46)),
    -- otherwise storage ≤ 770
    .mul (c r1) (not dp), mul3 dp (c fs) (c r1), mul3 dp (not (c fe)) (sub (n r1) (c fs)),
    mul3 (not (c big)) (c r1) (sub (k 770) (sum [c (dl 0), smul 256 (c st), bitsX 47 10])),
    mul3 (not (c big)) (sub (sub dp (c fs)) (c r1)) (c st),
    -- the read is not from the future
    mul3 dp (c fs) (sub (sub (c r) (c tprev)) (bitsX 57 9)) ] ++
  (List.range 7).map (fun j => mul3 dp (c fs) (d j)) ++
  (List.range 6).map (fun j => mul3 dp (not (c fe)) (sub (n (dl (j + 1))) (d j)))

/-! ## Claim rows -/

def cl : Expr := c sCL
def m1E : Expr := sub nPubE (k 1)

def cClaim : List Expr :=
  -- fixed claim prefix (protocol version 86, mainnet), n ≤ 256, nref < 2^16
  ((ZkFormal.Near.claimPrefix.zip (List.range 77)).map fun (x, j) => sub (.pub j) (k x.toNat)) ++
  [ .pub (PV_N + 2), .pub (PV_N + 3), Dsl.bool (.pub (PV_N + 1)), .mul (.pub (PV_N + 1)) (.pub PV_N),
    .pub (PV_NREF + 2), .pub (PV_NREF + 3),
    -- n ≥ 1
    .mul .isFirst (sub (.mul (.add (.pub PV_N) (.pub (PV_N + 1))) (c invA)) (k 1)),
    -- lanes below 8 / 4
    .mul .isFirst (not (c lo8)), .mul .isFirst (not (c lo4)),
    .mul (mul3 cl (not (c fe)) (n lo8)) (not (c lo8)),
    .mul (mul3 cl (not (c fe)) (n lo4)) (not (c lo4)),
    .mul (mul3 cl (c lo8) (not (n lo8))) (sub (c idx) (k 7)),
    .mul (mul3 cl (c lo4) (not (n lo4))) (sub (c idx) (k 3)),
    mul3 cl (c fe) (c lo8), mul3 cl (c fe) (c lo4),
    -- y = (n − 1)·G
    mul3 cl (c lo8) (sub (.add (.mul m1E (c (reg 16))) (c c1)) (.add (bitsX 0 8) (smul 256 (bitsX 8 8)))),
    .mul .isFirst (c c1), .mul (mul3 cl (c lo8) (not (c fe))) (sub (n c1) (bitsX 8 8)),
    .mul (mul3 cl (c lo8) (not (n lo8))) (bitsX 8 8),
    -- gasLimit − y − 1 ≥ 0
    mul3 cl (c lo8) (sub (sub (c (reg 24)) (bitsX 0 8))
      (sub (.add (c c2) (bitsX 16 8)) (smul 256 (c (xb 24))))),
    .mul .isFirst (sub (c c2) (k 1)), .mul (mul3 cl (c lo8) (not (c fe))) (sub (n c2) (c (xb 24))),
    .mul (mul3 cl (c lo8) (not (n lo8))) (c (xb 24)),
    -- gasBurnt = y + G = n·G
    mul3 cl (c lo8) (sub (sum [bitsX 0 8, c (reg 16), c c3]) (.add (c (tok 0)) (smul 256 (c (xb 25))))),
    .mul .isFirst (c c3), .mul (mul3 cl (c lo8) (not (c fe))) (sub (n c3) (c (xb 25))),
    .mul (mul3 cl (c lo8) (not (n lo8))) (c (xb 25)) ]

/-! ## End of the batch, digest lookups -/

def cEnd : List Expr :=
  [ .mul (c lastR) (sub (.add (c r) (k 1)) nPubE),
    .mul (c lastR) (sub (.add (c rcnt) (c hr)) nrefPubE) ] ++
  (List.range 16).map (fun j => .mul (c lastR) (sub (c (tok j)) (.pub (PV_TOK + j)))) ++
  [ sub (c gDg) (.mul (c fs) (.add (c sXRI) (c sXLH))),
    mul3 (c fs) (c sXRI) (sub (c dI) (mid K_RID (c r))), mul3 (c fs) (c sXRI) (sub (c dL) (k 48)),
    mul3 (c fs) (c sXLH) (sub (c dI) (mid K_PEO (c r))),
    mul3 (c fs) (c sXLH) (sub (c dL) (sum [k 37, smul 32 (c hr), c Lv])) ]

end ZkFormal.Near.Rcpt
