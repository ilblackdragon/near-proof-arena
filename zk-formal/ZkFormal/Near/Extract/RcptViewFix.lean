import ZkFormal.Near.Extract.RcptView

/-!
# ZkFormal.Near.Extract.RcptViewFix — `RcptViewStmt` with the fixes R-L6r-1..3

`RcptV.Wf'` / `RcptWf'` / `RcptViewStmt'` are `RcptV.Wf` / `RcptWf` /
`RcptViewStmt` (`Extract/RcptView.lean`) with the three corrections of
`docs/zk-formal/REQUESTS-L6.md`:

* R-L6r-1: `tprev_le` assumes `tprev < P − 512` (the table checks
  `r − tprev ∈ [0, 512)` in `Fp` only);
* R-L6r-2: the storage clause compares `(10^19 · st) mod 2^128` (the table's
  convolution is truncated at 16 bytes);
* R-L6r-3: `Wf` takes the block gas price as bytes `bgpB`, and `arith` assumes
  `Bytes8 bgpB` (in place of the vacuous `bgp < 2^128`).

Everything else is literally the original.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

structure RcptV.Wf' (x : RcptV) (r : Nat) (bgpB : List Nat) (tok tok' : Nat) : Prop where
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

structure RcptWf' (pub : List Fp) (rs : RcptVs) : Prop where
  toks : ∃ toks : List Nat, toks.length = rs.length + 1 ∧ toks.head? = some 0 ∧
    (∀ r (h : r < rs.length), rs[r].Wf' r (pubBytes pub PV_BGP 16) (toks.getD r 0) (toks.getD (r + 1) 0)) ∧
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

def RcptViewStmt' : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp), TableLocal Rcpt.table tr T_RCPT pub →
    ∃ rs, RcptWf' pub rs ∧ TableTraffic Rcpt.interactions tr T_RCPT pub (rcptTraffic pub rs)

end ZkFormal.Near
