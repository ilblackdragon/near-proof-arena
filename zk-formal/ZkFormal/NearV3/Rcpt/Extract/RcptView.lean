import ZkFormal.Near.Extract.RcptView
import ZkFormal.NearV3.Rcpt.Tables.Rcpt
import NearSpecV3.Layout

/-!
# ZkFormal.NearV3.Rcpt.Extract.RcptView — what `rcptV3` holds (`RcptV3ViewStmt`)

The view of `rcptV3` (`Tables/Rcpt*.lean`): the applied source lists in order (`ListV3`: the
two `n_j` bytes of the header and the list's receipts), each receipt a `RcptE` = v1's
`RcptV` (characters, ids, arithmetic, digests) plus the v3 data:

* `sys`, `ee`: system receipt, gas refund (`signer = receiver`);
* `gv`, `gs`, `sx`: the `SREC` gates of the receiver / signer rows and the received bytes;
* `akf`, `akk`, `aku`: the access-key walk's `FINAL` kind / value record and the `AKC` use
  count (meaningful with `ee`);
* `q`, `rlk`: the routing interval and the lookups `(pos, lo, hi, hn, u)` in row order.

Receipt indices `r` are global (flattened lists), `RC(j)` offsets restart at `12` per list,
body positions are global from `8`.  As in v1, raw bytes (range-checked by the SHA table or
the public bus) stay `List Nat`; facts that need byte values are stated under `Bytes8`
hypotheses.  The local facts are in `RcptE.Wf` / `RcptV3Wf`; linking (`Rcpt/Link/*`) turns
them and the bus balances into `NearSpecV3.applyReceipts`.
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpec.TransferV1

/-- One routing lookup `(pos, lo_pos, hi_pos, hn, u)`. -/
abbrev RLk := Nat × Nat × Nat × Nat × Nat

structure RcptE extends RcptV where
  sys : Bool
  ee : Bool
  gv : List Bool
  gs : List Bool
  sx : List Nat
  akf : Nat
  akk : Nat
  aku : Nat
  q : Nat
  rlk : List RLk
  deriving Repr, Inhabited

structure ListV3 where
  n0 : Nat
  n1 : Nat
  rs : List RcptE
  deriving Repr, Inhabited

abbrev RcptV3Vs := List ListV3

namespace RcptE
variable (x : RcptE)

/-- Key symbols of the access-key walk: `nibbles ([2] ‖ signer ‖ [2] ‖ kt ‖ pk) ++ [END]`. -/
def akSyms : List Nat :=
  ([2] ++ x.s ++ [2] ++ [x.kt] ++ x.pk).flatMap (fun ch => [ch / 16, ch % 16]) ++ [SYM_END]

def keyMsgs (w : Nat) (syms : List Nat) : List Msg :=
  (List.range syms.length).map fun t => [w, t, syms.getD t 0, if t + 1 = syms.length then 1 else 0]

end RcptE

/-! ## Positions -/

/-- All receipts, in applied order. -/
def flatR (ls : RcptV3Vs) : List RcptE := ls.flatMap (·.rs)

/-- Global index of the first receipt of list `j`. -/
def baseR (ls : RcptV3Vs) (j : Nat) : Nat := ((ls.take j).map (·.rs.length)).sum

/-- `RC(j)` offset of receipt `k` of a list (after the 12 header bytes). -/
def lOffs (rs : List RcptE) (k : Nat) : Nat := 12 + ((rs.take k).map (·.enc.length)).sum

/-- Body bytes of a receipt's refund (`0` without one). -/
def rfLen (x : RcptE) : Nat := if x.hr then x.encRefund.length else 0

/-- Body position of receipt `r`'s refund (global, after `u32 0 ‖ u32 nref`). -/
def bOffs (xs : List RcptE) (r : Nat) : Nat := 8 + ((xs.take r).map rfLen).sum

/-- Header bytes of list `L`: `u64 own ‖ u32 n_j` (as emitted). -/
def hdrBytes (pub : List Fp) (L : ListV3) : List Nat := pubBytes pub PH_OWN 8 ++ [L.n0, L.n1, 0, 0]

/-! ## Traffic -/

/-- Messages of receipt `x` = number `r` (global), `k`-th of list `j` with receipt list `rs`,
over all receipts `xs`. -/
def rSends (pub : List Fp) (xs : List RcptE) (j r o : Nat) (x : RcptE) (b : Nat) : List Msg :=
  if b = B_BYTES then
    emitAt (msgId K_RC j) o x.enc ++
    (if x.hr then emitAt K_RF (bOffs xs r) x.encRefund else []) ++
    emitAt (msgId K_PEO r) 0 x.peo ++ emitAt (msgId K_LEAF r) 0 x.leaf ++
    (if x.hr then emitAt (msgId K_RID r) 0 (x.rid ++ pubBytes pub PH_HEIGHT 8 ++ List.replicate 8 0)
     else [])
  else if b = B_KEYNIB then
    RcptE.keyMsgs r x.keySyms ++ (if x.ee then RcptE.keyMsgs (W_AK + r) x.akSyms else [])
  else if b = B_MEM then
    (List.range 16).map fun i => [x.kslot, r + 1, i, x.aft.getD i 0, x.lk.getD i 0, x.st.getD i 0]
  else if b = B_RIDS then (List.range 32).map fun i => [r, i, x.rid.getD i 0]
  else if b = B_MPOS then [[0, r, msgId K_LEAF r, 68]]
  else if b = B_SREC then
    ((List.range x.v.length).filter fun i => x.gv.getD i false).map fun i => [r, i, x.v.getD i 0]
  else if b = B_AKC then (if x.ee ∧ x.akf = 0 then [[x.akk, x.aku + 1]] else [])
  else if b = B_BND then
    x.rlk.map fun (p, l, h, hn, u) => [BND_STRIDE * x.q + p, l, h, hn, u + 1]
  else []

def rRecvs (r : Nat) (x : RcptE) (b : Nat) : List Msg :=
  if b = B_DIGEST then
    (if x.hr then [digMsg (msgId K_RID r) 48 x.rfid] else []) ++ [digMsg (msgId K_PEO r) x.peo.length x.peoh]
  else if b = B_FINAL then
    [r, 0, FK_VAL, x.kslot] :: (if x.ee then [[W_AK + r, 0, x.akf, x.akk]] else [])
  else if b = B_MEM then
    (List.range 16).map fun i => [x.kslot, x.tprev, i, x.bef.getD i 0, x.lk.getD i 0, x.st.getD i 0]
  else if b = B_SREC then
    ((List.range x.s.length).filter fun i => x.gs.getD i false).map fun i => [r, i, x.sx.getD i 0]
  else if b = B_AKC then (if x.ee ∧ x.akf = 0 then [[x.akk, x.aku]] else [])
  else if b = B_BND then
    x.rlk.map fun (p, l, h, hn, u) => [BND_STRIDE * x.q + p, l, h, hn, u]
  else []

/-- The receipts of list `j` with their global index and `RC(j)` offset. -/
def located (ls : RcptV3Vs) (j : Nat) : List (Nat × Nat × RcptE) :=
  let L := ls.getD j default
  (List.range L.rs.length).map fun k => (baseR ls j + k, lOffs L.rs k, L.rs.getD k default)

def rcptSends3 (pub : List Fp) (ls : RcptV3Vs) (b : Nat) : List Msg :=
  (List.range ls.length).flatMap fun j =>
    (if b = B_BYTES then emitAt (msgId K_RC j) 0 (hdrBytes pub (ls.getD j default)) else []) ++
    (if b = B_RCL then [[j, lOffs (ls.getD j default).rs (ls.getD j default).rs.length]] else []) ++
    (located ls j).flatMap fun (r, o, x) => rSends pub (flatR ls) j r o x b

def rcptRecvs3 (ls : RcptV3Vs) (b : Nat) : List Msg :=
  (List.range ls.length).flatMap fun j =>
    (located ls j).flatMap fun (r, _, x) => rRecvs r x b

def rcptTraffic3 (pub : List Fp) (ls : RcptV3Vs) : Traffic := ⟨rcptSends3 pub ls, rcptRecvs3 ls⟩

/-! ## Local facts -/

/-- `lo_i` / `hi_i` of a boundary string padded with the end marker `0`. -/
def padB (s : List Nat) (i : Nat) : Nat := s.getD i 0

/-- Routing: the lookups are positions `0, 1, …` (at most `Lv + 1`), and if they read the
records of a boundary pair `[lo, hi)` (missing `hi`: `hn = 1`), the receiver lies in it. -/
structure RouteOk (x : RcptE) : Prop where
  pos : x.rlk.map (·.1) = List.range x.rlk.length
  len : 1 ≤ x.rlk.length ∧ x.rlk.length ≤ x.v.length + 1
  sem : ∀ (lo hi : List Nat) (hn : Nat), (∀ y ∈ lo, 0 < y ∧ y < 256) → (∀ y ∈ hi, 0 < y ∧ y < 256) →
    lo.length ≤ 64 → hi.length ≤ 64 → hn ≤ 1 →
    (∀ e ∈ x.rlk, e.2.1 = padB lo e.1 ∧ e.2.2.1 = padB hi e.1 ∧ e.2.2.2.1 = hn) →
    NearSpecV3.lexLe (toBytes lo) (toBytes x.v) = true ∧
      (hn = 1 ∨ NearSpecV3.lexLe (toBytes hi) (toBytes x.v) = false)

/-- Per-receipt facts of `rcptV3` (v1's `RcptV.Wf` with system receipts, plus the v3 data). -/
structure RcptE.Wf (x : RcptE) (r : Nat) (bgpB : List Nat) (tok tok' : Nat) : Prop where
  lens : x.rid.length = 32 ∧ x.pk.length = 32 + 32 * x.kt ∧ x.kt ≤ 1 ∧ x.gp.length = 16 ∧
    x.dep.length = 16 ∧ x.bef.length = 16 ∧ x.lk.length = 16 ∧ x.st.length = 16 ∧
    x.aft.length = 16 ∧ x.burnt.length = 16 ∧ x.ramt.length = 16 ∧ x.rfid.length = 32 ∧
    x.peoh.length = 32 ∧ x.gv.length = x.v.length ∧ x.gs.length = x.s.length ∧
    x.sx.length = x.s.length
  ids : AccountId.valid (toBytes x.p) = true ∧ AccountId.valid (toBytes x.v) = true ∧
    AccountId.valid (toBytes x.s) = true ∧ Bytes8 x.p ∧ Bytes8 x.v ∧ Bytes8 x.s
  /-- `sys` is exactly "predecessor = system" -/
  sysIff : x.sys = true ↔ toBytes x.p = AccountId.system
  named : AccountId.isNamed (toBytes x.v) = true
  aft8 : Bytes8 x.aft
  small : x.kslot < P ∧ x.tprev < P ∧ x.akk < P ∧ x.aku < P ∧ x.q < P
  tprev_le : x.tprev < P - 512 → x.tprev ≤ r
  arith : Bytes8 bgpB → Bytes8 x.gp → Bytes8 x.dep → Bytes8 x.bef → Bytes8 x.lk → Bytes8 x.st →
    Bytes8 x.burnt → (x.hr = true → Bytes8 x.ramt) →
    leN' x.aft = leN' x.bef + leN' x.dep ∧ leN' x.aft < Params.u128Max ∧
    leN' x.aft + leN' x.lk < Params.two128 ∧
    ((Params.storageAmountPerByte * leN' x.st) % Params.two128 ≤ leN' x.aft + leN' x.lk ∨
      leN' x.st ≤ Params.zeroBalanceStorageLimit) ∧
    (x.ge = decide (leN' bgpB ≤ leN' x.gp)) ∧
    leN' x.burnt = (if x.sys then 0 else Params.G * min (leN' x.gp) (leN' bgpB)) ∧
    (x.hr = true ↔ x.sys = false ∧ Params.G * (leN' x.gp - min (leN' x.gp) (leN' bgpB)) ≠ 0) ∧
    (x.hr = true → leN' x.ramt = Params.G * (leN' x.gp - min (leN' x.gp) (leN' bgpB))) ∧
    tok' = tok + leN' x.burnt ∧ tok' < Params.two128
  /-- gas refund: `ee ⇒ sys`, equal lengths, every receiver / signer row in `SREC`, the
  signer rows receive their own bytes -/
  ee : x.ee = true → x.sys = true ∧ x.s.length = x.v.length ∧ (∀ i < x.v.length, x.gv.getD i false = true) ∧
    (∀ i < x.s.length, x.gs.getD i false = true) ∧ ∀ i < x.s.length, x.sx.getD i 0 = x.s.getD i 0
  /-- a system receipt without `ee`: different lengths, or a signer row whose received byte
  differs from its own -/
  neq : x.sys = true → x.ee = false → x.s.length ≠ x.v.length ∨
    ∃ i < x.s.length, x.gs.getD i false = true ∧ x.sx.getD i 0 ≠ x.s.getD i 0
  akf : x.akf ≤ 1
  route : RouteOk x

/-- All raw values of a receipt segment. -/
def RcptE.raw3 (x : RcptE) : List Nat :=
  x.raw ++ x.sx ++ [x.akf, x.akk, x.aku, x.q] ++
    x.rlk.flatMap fun (p, l, h, hn, u) => [p, l, h, hn, u]

/-- Table-level facts (header facts for byte-valued public inputs). -/
structure RcptV3Wf (pub : List Fp) (ls : RcptV3Vs) : Prop where
  nonempty : ls ≠ []
  toks : ∃ toks : List Nat, toks.length = (flatR ls).length + 1 ∧ toks.head? = some 0 ∧
    (∀ r (h : r < (flatR ls).length),
      (flatR ls)[r].Wf r (pubBytes pub PH_GP 16) (toks.getD r 0) (toks.getD (r + 1) 0)) ∧
    ((∀ i, i < 16 → pubNat pub (PH_BURNT + i) < 256) →
      toks.getD (flatR ls).length 0 = leN' (pubBytes pub PH_BURNT 16))
  count : (∀ i, i < 4 → pubNat pub (PH_N + i) < 256) → (flatR ls).length = leN' (pubBytes pub PH_N 4)
  /-- the header's `n_j` bytes encode the list length (in the field) -/
  nj : ∀ L ∈ ls, Fp.ofNat (L.n0 + 256 * L.n1) = Fp.ofNat L.rs.length
  /-- the body has `|B| − 8` refund bytes -/
  body : (∀ i, i < 4 → pubNat pub (PH_BLEN + i) < 256) →
    bOffs (flatR ls) (flatR ls).length = leN' (pubBytes pub PH_BLEN 4)
  canon : (∀ L ∈ ls, L.n0 < P ∧ L.n1 < P) ∧ ∀ x ∈ flatR ls, ∀ y ∈ x.raw3, y < P

/-- **The `rcptV3` view statement.** -/
def RcptV3ViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal RcptV3.table tr t pub →
    ∃ ls, RcptV3Wf pub ls ∧ TableTraffic RcptV3.interactions tr t pub (rcptTraffic3 pub ls)

end ZkFormal.NearV3
