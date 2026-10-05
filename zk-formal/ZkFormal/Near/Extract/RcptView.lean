import ZkFormal.Near.Extract.Common

/-!
# ZkFormal.Near.Extract.RcptView — what the `rcpt` table holds

One `RcptV` per receipt segment, in batch order.  Raw bytes (range-checked by
the SHA table, not here) stay `List Nat`; the arithmetic and claim facts are
stated for byte values (`Bytes8` hypotheses), which linking discharges from
the SHA contract.  Account-id characters are range-checked locally (nibble
split), so the account-id grammar facts are unconditional.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

structure RcptV where
  /-- predecessor, receiver, signer characters -/
  p : List Nat
  v : List Nat
  s : List Nat
  rid : List Nat
  kt : Nat
  pk : List Nat
  gp : List Nat
  dep : List Nat
  /-- refund flag, `gas_price ≥ block_gas_price` -/
  hr : Bool
  ge : Bool
  /-- receiver's slot (from `FINAL`) and the time of its memory read -/
  kslot : Nat
  tprev : Nat
  /-- memory read payload: amount, locked, storage bytes -/
  bef : List Nat
  lk : List Nat
  st : List Nat
  /-- amount after, burnt, refund amount (16 bytes each) -/
  aft : List Nat
  burnt : List Nat
  ramt : List Nat
  /-- refund id and `H(PEO)` windows -/
  rfid : List Nat
  peoh : List Nat
  deriving Repr, Inhabited

def G_LEn : List Nat := [196, 164, 183, 246, 51, 0, 0, 0]
def tailN : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3]
def systemN : List Nat := [115, 121, 115, 116, 101, 109]

namespace RcptV
variable (x : RcptV)

def borshN (s : List Nat) : List Nat := u32r s.length ++ s

/-- The receipt's encoding as the `RC` rows emit it. -/
def enc : List Nat :=
  borshN x.p ++ borshN x.v ++ x.rid ++ [0] ++ borshN x.s ++ [x.kt] ++ x.pk ++ x.gp ++ tailN ++ x.dep

/-- The refund receipt's encoding (`RF` rows). -/
def encRefund : List Nat :=
  [6, 0, 0, 0] ++ systemN ++ borshN x.s ++ x.rfid ++ [0] ++ borshN x.s ++ [x.kt] ++ x.pk ++
    List.replicate 16 0 ++ tailN ++ x.ramt

def peo : List Nat :=
  u32r (if x.hr then 1 else 0) ++ (if x.hr then x.rfid else []) ++ G_LEn ++ x.burnt ++ borshN x.v ++
    [2, 0, 0, 0, 0]

def leaf : List Nat := [2, 0, 0, 0] ++ x.rid ++ x.peoh

/-- Key symbols of the receiver: `nibbles (0x00 ‖ v) ++ [END]`. -/
def keySyms : List Nat := [0, 0] ++ x.v.flatMap (fun ch => [ch / 16, ch % 16]) ++ [SYM_END]

end RcptV

/-- The whole table: the receipts. -/
abbrev RcptVs := List RcptV

def rcOffs (rs : RcptVs) : Nat → Nat
  | 0 => 12
  | r + 1 => rcOffs rs r + (rs.getD r default).enc.length

def rfOffs (rs : RcptVs) : Nat → Nat
  | 0 => 4
  | r + 1 => rfOffs rs r + (if (rs.getD r default).hr then (rs.getD r default).encRefund.length else 0)

def pubBytes (pub : List Fp) (off len : Nat) : List Nat := (List.range len).map fun j => pubNat pub (off + j)

def rcptSends (pub : List Fp) (rs : RcptVs) (b : Nat) : List Msg :=
  let rr := rs.zip (List.range rs.length)
  if b = B_BYTES then
    emitAt K_RC 0 (pubBytes pub PV_SHARD 8 ++ pubBytes pub PV_N 4) ++
    emitAt K_RF 0 (pubBytes pub PV_NREF 4) ++
    rr.flatMap fun (x, r) =>
      emitAt K_RC (rcOffs rs r) x.enc ++
      (if x.hr then emitAt K_RF (rfOffs rs r) x.encRefund else []) ++
      emitAt (msgId K_PEO r) 0 x.peo ++ emitAt (msgId K_LEAF r) 0 x.leaf ++
      (if x.hr then emitAt (msgId K_RID r) 0 (x.rid ++ pubBytes pub PV_HEIGHT 8 ++ List.replicate 8 0)
       else [])
  else if b = B_KEYNIB then
    rr.flatMap fun (x, r) => (List.range x.keySyms.length).map fun t =>
      [r, t, x.keySyms.getD t 0, if t + 1 = x.keySyms.length then 1 else 0]
  else if b = B_MEM then
    rr.flatMap fun (x, r) => (List.range 16).map fun i =>
      [x.kslot, r + 1, i, x.aft.getD i 0, x.lk.getD i 0, x.st.getD i 0]
  else if b = B_RIDS then
    rr.flatMap fun (x, r) => (List.range 32).map fun i => [r, i, x.rid.getD i 0]
  else if b = B_MPOS then
    rr.map fun (_, r) => [0, r, msgId K_LEAF r, 68]
  else []

def rcptRecvs (pub : List Fp) (rs : RcptVs) (b : Nat) : List Msg :=
  let rr := rs.zip (List.range rs.length)
  if b = B_DIGEST then
    [digMsg K_RC (rcOffs rs rs.length) (pubBytes pub PV_RC 32),
     digMsg K_RF (rfOffs rs rs.length) (pubBytes pub PV_RFC 32)] ++
    rr.flatMap fun (x, r) =>
      (if x.hr then [digMsg (msgId K_RID r) 48 x.rfid] else []) ++
      [digMsg (msgId K_PEO r) x.peo.length x.peoh]
  else if b = B_FINAL then rr.map fun (x, r) => [r, x.kslot]
  else if b = B_MEM then
    rr.flatMap fun (x, r) => (List.range 16).map fun i =>
      [x.kslot, x.tprev, i, x.bef.getD i 0, x.lk.getD i 0, x.st.getD i 0]
  else []

def rcptTraffic (pub : List Fp) (rs : RcptVs) : Traffic := ⟨rcptSends pub rs, rcptRecvs pub rs⟩

/-! ## Local facts -/

/-- Every value of the list is a byte. -/
def Bytes8 (l : List Nat) : Prop := ∀ y ∈ l, y < 256

def leN' (l : List Nat) : Nat := leNat (l.map UInt8.ofNat)
def toBytes (l : List Nat) : Bytes := l.map UInt8.ofNat

/-- Per-receipt facts; `bgpB` are the block gas price bytes and `tok`/`tok'` the
tokens burnt before / after this receipt (as naturals).  (Fixes R-L6r-1..3 of
`REQUESTS-L6.md`: `tprev_le` assumes `tprev < P − 512`; the storage clause is
mod `2^128`; `arith` assumes the gas price bytes are bytes.) -/
structure RcptV.Wf (x : RcptV) (r : Nat) (bgpB : List Nat) (tok tok' : Nat) : Prop where
  lens : x.rid.length = 32 ∧ x.pk.length = 32 + 32 * x.kt ∧ x.kt ≤ 1 ∧ x.gp.length = 16 ∧
    x.dep.length = 16 ∧ x.bef.length = 16 ∧ x.lk.length = 16 ∧ x.st.length = 16 ∧
    x.aft.length = 16 ∧ x.burnt.length = 16 ∧ x.ramt.length = 16 ∧ x.rfid.length = 32 ∧
    x.peoh.length = 32
  ids : AccountId.valid (toBytes x.p) = true ∧ AccountId.valid (toBytes x.v) = true ∧
    AccountId.valid (toBytes x.s) = true ∧ Bytes8 x.p ∧ Bytes8 x.v ∧ Bytes8 x.s
  notSystem : toBytes x.p ≠ AccountId.system
  named : AccountId.isNamed (toBytes x.v) = true
  aft8 : Bytes8 x.aft
  small : x.kslot < P ∧ x.tprev < P
  /-- R-L6r-1 -/
  tprev_le : x.tprev < P - 512 → x.tprev ≤ r
  /-- R-L6r-2, R-L6r-3 -/
  arith : Bytes8 bgpB → Bytes8 x.gp → Bytes8 x.dep → Bytes8 x.bef → Bytes8 x.lk → Bytes8 x.st →
    Bytes8 x.burnt → (x.hr = true → Bytes8 x.ramt) →
    leN' x.aft = leN' x.bef + leN' x.dep ∧ leN' x.aft < Params.u128Max ∧
    leN' x.aft + leN' x.lk < Params.two128 ∧
    ((Params.storageAmountPerByte * leN' x.st) % Params.two128 ≤ leN' x.aft + leN' x.lk ∨
      leN' x.st ≤ Params.zeroBalanceStorageLimit) ∧
    (x.ge = decide (leN' bgpB ≤ leN' x.gp)) ∧
    leN' x.burnt = Params.G * min (leN' x.gp) (leN' bgpB) ∧
    (x.hr = true ↔ Params.G * (leN' x.gp - min (leN' x.gp) (leN' bgpB)) ≠ 0) ∧
    (x.hr = true → leN' x.ramt = Params.G * (leN' x.gp - min (leN' x.gp) (leN' bgpB))) ∧
    tok' = tok + leN' x.burnt ∧ tok' < Params.two128

/-- `n` from the public claim bytes (little endian). -/
def nPubLE (pub : List Fp) : Nat := leN' (pubBytes pub PV_N 4)

/-- All raw values of a receipt segment. -/
def RcptV.raw (x : RcptV) : List Nat :=
  x.p ++ x.v ++ x.s ++ x.rid ++ [x.kt] ++ x.pk ++ x.gp ++ x.dep ++ x.bef ++ x.lk ++ x.st ++ x.aft ++
    x.burnt ++ x.ramt ++ x.rfid ++ x.peoh

/-- Table-level facts (claim facts stated for byte-valued public inputs, as
`publicOf` provides). -/
structure RcptWf (pub : List Fp) (rs : RcptVs) : Prop where
  toks : ∃ toks : List Nat, toks.length = rs.length + 1 ∧ toks.head? = some 0 ∧
    (∀ r (h : r < rs.length), rs[r].Wf r (pubBytes pub PV_BGP 16) (toks.getD r 0) (toks.getD (r + 1) 0)) ∧
    ((∀ i, i < 16 → pubNat pub (PV_TOK + i) < 256) →
      toks.getD rs.length 0 = leN' (pubBytes pub PV_TOK 16))
  prefix_ : ∀ j, j < 77 → pubNat pub j = (ZkFormal.Near.claimPrefix.getD j 0).toNat
  count : (∀ x, x < 4 → pubNat pub (PV_N + x) < 256) → rs.length = nPubLE pub ∧ 1 ≤ rs.length ∧
    rs.length ≤ 256
  gasLimit : (∀ j, j < 309 → pubNat pub j < 256) →
    (rs.length - 1) * Params.G < leN' (pubBytes pub PV_GASLIM 8) ∧
    leN' (pubBytes pub PV_GAS 8) = rs.length * Params.G
  refunds : (∀ j, j < 309 → pubNat pub j < 256) →
    (rs.filter (·.hr)).length = leN' (pubBytes pub PV_NREF 4)
  canon : ∀ x ∈ rs, ∀ y ∈ x.raw, y < P

def RcptViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp), TableLocal Rcpt.table tr T_RCPT pub →
    ∃ rs, RcptWf pub rs ∧ TableTraffic Rcpt.interactions tr T_RCPT pub (rcptTraffic pub rs)

end ZkFormal.Near
