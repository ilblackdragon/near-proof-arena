import ZkFormal.Near.Render.RcptSim
import ZkFormal.Near.Tables.Rcpt

/-!
# ZkFormal.Near.Render.Rcpt — honest rows of the `rcpt` table

12 claim rows, one segment per receipt (fields
`PL P VL V RID T0 SL S KT PK GP TL DEP XP0 [XRI] XG XST XL0 XLH [XRH XRF XRZ]`),
then at least one padding row.  Follows `Tables/Rcpt.lean` and
`Tables/Rcpt/{Layout,Fields,Arith}.lean`: registers loaded at a field's first
row and shifted, account-id character machinery, key symbols, byte-serial gas
and balance arithmetic (carries, borrows, delay lines, bit pools in `xb`),
claim checks.  The emission slots are filled by evaluating the table's own
`emits` expressions on the finished row.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air

namespace RcptGen

open ZkFormal.Near.Rcpt (act rf rl lastR sCL sPL sP sVL sV sRID sT0 sSL sS sKT sPK sGP sTL sDEP
  sXP0 sXRI sXG sXST sXL0 sXLH sXRH sXRF sXRZ idx fs fe b tA symA lastA gKA kz r o o2 Lp Lv Ls
  kt hr kslot tprev rcnt ge big oEnd o2End reg tok h2 h3 h5 h6 h7 lb z linv l210 hx6 acc vc0
  vc1 h01 p1 p2 p3 i1 i2 i3 isys r1 lo8 lo4 xb c1 c2 c3 c4 dl burnt ramt sumD invA bef lk st
  dsum invB dI dL gDg eId ePos eV eG emits G_LE S_LE)

/-- Value of an expression on a row (current-row columns, constants, public
inputs; `next`/selectors read as `0` — `emits` uses neither). -/
def evalRow (row : Row) (pub : Array Nat) : Expr → Nat
  | .const v => v % P
  | .col x false => row.getD x 0 % P
  | .col _ true => 0
  | .pub i => pub.getD i 0 % P
  | .isFirst | .isLast | .isTransition => 0
  | .add a d => (evalRow row pub a + evalRow row pub d) % P
  | .mul a d => (evalRow row pub a * evalRow row pub d) % P
  | .neg a => (P - evalRow row pub a % P) % P

def b2n (x : Bool) : Nat := if x then 1 else 0
def bitOf (x j : Nat) : Nat := (x / 2 ^ j) % 2

/-- Set `len` bits of `x` into `xb off …`. -/
def setBits (row : Row) (off len x : Nat) : Row :=
  (List.range len).foldl (fun rw j => rw.set! (xb (off + j)) (bitOf x j)) row

/-- `(sum of a little-endian convolution) ` helper: `Σ_j g_j · v_{i−j}`. -/
def conv (g : List Nat) (v : List Nat) (i : Nat) : Nat :=
  (List.range g.length).foldl (fun a j => if j ≤ i then a + g.getD j 0 * v.getD (i - j) 0 else a) 0

/-- Character columns of an account-id byte. -/
def setChar (row : Row) (ch : Nat) : Row := Id.run do
  let hi := ch / 16
  let lo := ch % 16
  let mut rw := row
  for (col, v) in [(h2, 2), (h3, 3), (h5, 5), (h6, 6), (h7, 7)] do
    rw := rw.set! col (b2n (hi == v))
  for j in List.range 4 do rw := rw.set! (lb j) (bitOf lo j)
  rw := rw.set! z (b2n (lo == 0))
  rw := rw.set! linv (if lo == 0 then 0 else invP lo)
  rw := rw.set! l210 (b2n (lo % 8 == 7))
  rw := rw.set! hx6 (b2n (hi == 6 && 1 ≤ lo && lo ≤ 6))
  return rw

def isHexC (ch : Nat) : Bool := (48 ≤ ch && ch ≤ 57) || (97 ≤ ch && ch ≤ 102)

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

/-- Field plan: `(state, length, register load)`. -/
def plan (d : RD) (pub : Array Nat) : List (Nat × Nat × List Nat) :=
  let pubs (off len : Nat) := (List.range len).map fun j => pub.getD (off + j) 0
  [ (sPL, 4, [d.pred.length, 0, 0, 0]), (sP, d.pred.length, [115, 121, 115, 116, 101, 109]),
    (sVL, 4, [d.recv.length, 0, 0, 0]), (sV, d.recv.length, []), (sRID, 32, []),
    (sT0, 1, [0]), (sSL, 4, [d.signer.length, 0, 0, 0]), (sS, d.signer.length, []),
    (sKT, 1, [d.kt]), (sPK, 32 + 32 * d.kt, []), (sGP, 16, pubs PV_BGP 16),
    (sTL, 13, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3]), (sDEP, 16, []),
    (sXP0, 4, [b2n d.hr, 0, 0, 0]) ] ++
  (if d.hr then [(sXRI, 32, d.refundId)] else []) ++
  [ (sXG, 8, G_LE), (sXST, 5, [2, 0, 0, 0, 0]), (sXL0, 4, [2, 0, 0, 0]), (sXLH, 32, d.peoDig) ] ++
  (if d.hr then
    [(sXRH, 16, pubs PV_HEIGHT 8 ++ List.replicate 8 0),
     (sXRF, 10, [6, 0, 0, 0, 115, 121, 115, 116, 101, 109]), (sXRZ, 16, List.replicate 16 0)]
   else [])

def regStates : List Nat := ZkFormal.Near.Rcpt.regStates

/-- Rows of one receipt segment. -/
def segRows (d : RD) (pub : Array Nat) (bgpB : List Nat) : Array Row := Id.run do
  let pl := plan d pub
  let gpB := leBytes 16 d.gp
  let depB := leBytes 16 d.dep
  let befB := leBytes 16 d.bef
  let lkB := leBytes 16 d.locked
  let stB := leBytes 8 d.stor
  let aft := d.bef + d.dep
  let aftB := leBytes 16 aft
  let totB := leBytes 16 (aft + d.locked)
  let qB := leBytes 16 (10000000000000000000 * d.stor)
  let pB := (List.range 16).map fun i => if d.ge then bgpB.getD i 0 else gpB.getD i 0
  -- gas: gp − bgp with borrow
  let gpDiff : List (Nat × Nat × Nat) := Id.run do   -- (borrow-in, D, borrow-out)
    let mut out : Array (Nat × Nat × Nat) := #[]
    let mut br : Nat := 0
    for i in List.range 16 do
      let t : Int := (gpB.getD i 0 : Int) - bgpB.getD i 0 - br
      let (dv, bo) := if t < 0 then ((t + 256).toNat, 1) else (t.toNat, 0)
      out := out.push (br, dv, bo)
      br := bo
    return out.toList
  let surB := gpDiff.map fun (_, dv, _) => if d.ge then dv else 0
  let tokOld := leBytes 16 d.tok0
  let tokNew := leBytes 16 (d.tok0 + d.burnt)
  let oEndV := d.o + 123 + d.pred.length + d.recv.length + d.signer.length + 32 * d.kt
  let o2EndV := d.o2 + (if d.hr then 129 + 2 * d.signer.length + 32 * d.kt else 0)
  let base : Row := Id.run do
    let mut rw := zeroRow Rcpt.width
    rw := rw.set! act 1
    for (col, v) in [(r, d.r), (o, d.o), (o2, d.o2), (Lp, d.pred.length), (Lv, d.recv.length),
        (Ls, d.signer.length), (kt, d.kt), (hr, b2n d.hr), (kslot, d.kslot), (tprev, d.tprev),
        (rcnt, d.rcnt), (ge, b2n d.ge), (big, b2n d.big), (oEnd, oEndV), (o2End, o2EndV)] do
      rw := rw.set! col v
    return rw
  let mut rows : Array Row := #[]
  let nf := pl.length
  for ((s, len, ld), fi) in pl.zip (List.range nf) do
    -- carries / running values within the field
    let mut cc1 : Nat := 0
    let mut cc2 : Nat := 0
    let mut cc3 : Nat := 0
    let mut cc4 : Nat := 0
    let mut runD : Nat := 0
    let mut runA : Nat := 0
    let mut accV : Nat := 0
    let str := if s == sP then d.pred else if s == sV then d.recv else d.signer
    for i in List.range len do
      let mut rw := base
      rw := rw.set! s 1
      rw := rw.set! idx i
      rw := rw.set! fs (b2n (i == 0))
      rw := rw.set! fe (b2n (i + 1 == len))
      let isRl := i + 1 == len && fi + 1 == nf
      rw := rw.set! rl (b2n isRl)
      rw := rw.set! rf (b2n (s == sPL && i == 0))
      for j in List.range 32 do rw := rw.set! (reg j) (ld.getD (i + j) 0)
      -- tokens register: old bytes before GP, rotated in GP, new bytes after
      let fieldsBeforeGP := s == sPL || s == sP || s == sVL || s == sV || s == sRID || s == sT0 ||
        s == sSL || s == sS || s == sKT || s == sPK
      for j in List.range 16 do
        let v := if fieldsBeforeGP then tokOld.getD j 0
          else if s == sGP then (if i + j < 16 then tokOld.getD (i + j) 0 else tokNew.getD (i + j - 16) 0)
          else tokNew.getD j 0
        rw := rw.set! (tok j) v
      -- the row's byte
      let bv : Nat :=
        if regStates.contains s then ld.getD i 0
        else if s == sP || s == sV || s == sS then str.getD i 0
        else if s == sRID then d.id.getD i 0
        else if s == sPK then d.pk.getD i 0
        else if s == sGP then gpB.getD i 0
        else if s == sDEP then depB.getD i 0
        else 0
      rw := rw.set! b bv
      -- account ids
      if s == sP || s == sV || s == sS then
        rw := setChar rw bv
        if i + 1 == len then
          rw := setBits rw 0 6 (len - 2)
          rw := setBits rw 6 6 (64 - len)
      if s == sP then
        let dd : Int := (bv : Int) - (ld.getD i 0 : Int)
        accV := accV + (dd * dd).toNat
        rw := rw.set! acc (accV % P)
        if i + 1 == len then
          let l6 : Int := (len : Int) - 6
          let pv := (accV + (l6 * l6).toNat) % P
          rw := rw.set! p1 pv
          rw := rw.set! isys (invP pv)
      if s == sV then
        accV := accV + b2n (isHexC bv)
        rw := rw.set! acc accV
        let v0 := d.recv.getD 0 0
        let v1 := d.recv.getD 1 0
        rw := rw.set! vc0 v0
        rw := rw.set! vc1 v1
        let h01v := b2n (isHexC v0) + b2n (isHexC v1)
        rw := rw.set! h01 h01v
        if i + 1 == len then
          let sq (x : Int) : Nat := (x * x).toNat
          let L : Int := len
          let a : Int := accV
          let pv1 := (sq (L - 64) + sq (a - L)) % P
          let pv2 := (sq (L - 42) + sq ((v0 : Int) - 48) + sq ((v1 : Int) - 120) + sq (a - h01v - 40)) % P
          let pv3 := (sq (L - 42) + sq ((v0 : Int) - 48) + sq ((v1 : Int) - 115) + sq (a - h01v - 40)) % P
          rw := rw.set! p1 pv1
          rw := rw.set! p2 pv2
          rw := rw.set! p3 pv3
          rw := rw.set! i1 (invP pv1)
          rw := rw.set! i2 (invP pv2)
          rw := rw.set! i3 (invP pv3)
      -- key symbols (slot A)
      if s == sV then
        rw := rw.set! gKA 1
        rw := rw.set! tA (2 + 2 * i)
        rw := rw.set! symA (bv / 16)
      if s == sVL && i < 2 then
        rw := rw.set! kz 1
        rw := rw.set! gKA 1
        rw := rw.set! tA i
      if s == sRID && i == 0 then
        rw := rw.set! gKA 1
        rw := rw.set! tA (2 + 2 * d.recv.length)
        rw := rw.set! symA SYM_END
        rw := rw.set! lastA 1
      -- digest windows
      if i == 0 && (s == sXRI || s == sXLH) then
        rw := rw.set! gDg 1
        rw := rw.set! dI (if s == sXRI then msgId K_RID d.r else msgId K_PEO d.r)
        rw := rw.set! dL (if s == sXRI then 48 else d.peoLen)
      -- gas
      if s == sGP then
        let (bin, dv, bo) := gpDiff.getD i (0, 0, 0)
        rw := rw.set! c1 bin
        rw := setBits rw 0 8 dv
        rw := setBits rw 8 1 bo
        let sb := conv (G_LE.take 5) pB i + cc2
        rw := rw.set! c2 cc2
        rw := rw.set! burnt (sb % 256)
        rw := setBits rw 9 11 (sb / 256)
        cc2 := sb / 256
        let sr := conv (G_LE.take 5) surB i + cc3
        rw := rw.set! c3 cc3
        rw := rw.set! ramt (sr % 256)
        rw := setBits rw 20 11 (sr / 256)
        cc3 := sr / 256
        let tt := tokOld.getD i 0 + sb % 256 + cc4
        rw := rw.set! c4 cc4
        rw := setBits rw 31 8 (tt % 256)
        rw := setBits rw 39 1 (tt / 256)
        cc4 := tt / 256
        runD := runD + dv
        rw := rw.set! sumD runD
        if i + 1 == len then rw := rw.set! invA (if d.hr then invP runD else 0)
        for j in List.range 4 do
          rw := rw.set! (dl j) (if j < i then pB.getD (i - 1 - j) 0 else 0)
          rw := rw.set! (dl (4 + j)) (if j < i then surB.getD (i - 1 - j) 0 else 0)
      -- balances
      if s == sDEP then
        rw := rw.set! bef (befB.getD i 0)
        rw := rw.set! lk (lkB.getD i 0)
        rw := rw.set! st (stB.getD i 0)
        let sa := befB.getD i 0 + depB.getD i 0 + cc1
        rw := rw.set! c1 cc1
        rw := setBits rw 0 8 (sa % 256)
        rw := setBits rw 8 1 (sa / 256)
        cc1 := sa / 256
        runA := runA + (255 - aftB.getD i 0)
        rw := rw.set! dsum runA
        if i + 1 == len then rw := rw.set! invB (invP runA)
        let stt := aftB.getD i 0 + lkB.getD i 0 + cc2
        rw := rw.set! c2 cc2
        rw := setBits rw 9 8 (stt % 256)
        rw := setBits rw 17 1 (stt / 256)
        cc2 := stt / 256
        let sq := conv S_LE stB i + cc3
        rw := rw.set! c3 cc3
        rw := setBits rw 18 8 (sq % 256)
        rw := setBits rw 26 12 (sq / 256)
        cc3 := sq / 256
        let tq : Int := (totB.getD i 0 : Int) - qB.getD i 0 - cc4
        let (dv, bo) := if tq < 0 then ((tq + 256).toNat, 1) else (tq.toNat, 0)
        rw := rw.set! c4 cc4
        rw := setBits rw 38 8 dv
        rw := setBits rw 46 1 bo
        cc4 := bo
        rw := rw.set! r1 (b2n (i == 1))
        if i == 1 && !d.big then
          rw := setBits rw 47 10 (770 - (stB.getD 0 0 + 256 * stB.getD 1 0))
        if i == 0 then rw := setBits rw 57 9 (d.r - d.tprev)
        for j in List.range 7 do
          rw := rw.set! (dl j) (if j < i then stB.getD (i - 1 - j) 0 else 0)
      rows := rows.push rw
  return rows

/-- Claim rows. -/
def claimRows (pub : Array Nat) : Array Row := Id.run do
  let pubs (off len : Nat) := (List.range len).map fun j => pub.getD (off + j) 0
  let A := pubs PV_SHARD 8 ++ pubs PV_N 4
  let B := pubs PV_NREF 4
  let C := G_LE
  let D := pubs PV_GASLIM 8
  let T := pubs PV_GAS 8
  let n := (pubs PV_N 4).foldr (fun x a => x + 256 * a) 0
  let yB := leBytes 8 ((n - 1) * Params.G)
  let mut rows : Array Row := #[]
  let mut cc1 : Nat := 0
  let mut cc2 : Nat := 1
  let mut cc3 : Nat := 0
  for i in List.range 12 do
    let mut rw := zeroRow Rcpt.width
    rw := rw.set! act 1
    rw := rw.set! sCL 1
    rw := rw.set! idx i
    rw := rw.set! fs (b2n (i == 0))
    rw := rw.set! fe (b2n (i == 11))
    for j in List.range 12 do rw := rw.set! (reg j) (A.getD ((i + j) % 12) 0)
    for j in List.range 4 do rw := rw.set! (reg (12 + j)) (B.getD ((i + j) % 4) 0)
    for j in List.range 8 do
      rw := rw.set! (reg (16 + j)) (C.getD ((i + j) % 8) 0)
      rw := rw.set! (reg (24 + j)) (D.getD ((i + j) % 8) 0)
      rw := rw.set! (tok j) (T.getD ((i + j) % 8) 0)
    rw := rw.set! lo8 (b2n (i < 8))
    rw := rw.set! lo4 (b2n (i < 4))
    if i == 0 then rw := rw.set! invA (invP (pub.getD PV_N 0 + pub.getD (PV_N + 1) 0))
    if i < 8 then
      let sy := (n - 1) * C.getD i 0 + cc1
      rw := rw.set! c1 cc1
      rw := setBits rw 0 8 (sy % 256)
      rw := setBits rw 8 8 (sy / 256)
      cc1 := sy / 256
      let td : Int := (D.getD i 0 : Int) - yB.getD i 0 - cc2
      let (dv, bo) := if td < 0 then ((td + 256).toNat, 1) else (td.toNat, 0)
      rw := rw.set! c2 cc2
      rw := setBits rw 16 8 dv
      rw := setBits rw 24 1 bo
      cc2 := bo
      let sg := yB.getD i 0 + C.getD i 0 + cc3
      rw := rw.set! c3 cc3
      rw := setBits rw 25 1 (sg / 256)
      cc3 := sg / 256
    rows := rows.push rw
  return rows

/-- Fill the emission slots of a row from the table's `emits`. -/
def fillEmits (pub : Array Nat) (rw : Row) : Row := Id.run do
  let mut rw := rw
  for (s, ems) in emits do
    if rw.getD s 0 == 1 then
      for (em, e) in ems.zip (List.range ems.length) do
        let (id, p, v, g) := em
        rw := rw.set! (eId e) (evalRow rw pub id)
        rw := rw.set! (ePos e) (evalRow rw pub p)
        rw := rw.set! (eV e) (evalRow rw pub v)
        rw := rw.set! (eG e) (evalRow rw pub g)
  return rw

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

open RcptGen in
/-- Honest rows of the `rcpt` table (padded, at least one padding row). -/
def rcptRowsAll (I : Info) : Array Row := Id.run do
  let pub : Array Nat := (toNats I.c.encode).toArray
  let bgpB := leBytes 16 I.c.blockGasPrice
  let ds := rcptData I
  let mut rows := claimRows pub
  for d in ds do rows := rows ++ segRows d pub bgpB
  -- the batch's last row
  if rows.size > 0 then
    rows := rows.modify (rows.size - 1) (·.set! Rcpt.lastR 1)
  rows := rows.map (fillEmits pub)
  return padTo (rows.push (zeroRow Rcpt.width)) (zeroRow Rcpt.width)

end ZkFormal.Near.Render
