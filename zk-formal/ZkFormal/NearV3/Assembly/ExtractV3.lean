import ZkFormal.NearV3.Assembly.NearAir
import ZkFormal.NearV3.Assembly.NearAirCheck
import ZkFormal.Near.Extract.Common
import ZkFormal.NearV3.Extract.NodeView
import ZkFormal.NearV3.Extract.WalkView
import ZkFormal.NearV3.Extract.HeadProof
import ZkFormal.NearV3.Extract.ValProof
import ZkFormal.NearV3.Extract.UniqProof
import ZkFormal.NearV3.Extract.Ups.View
import ZkFormal.NearV3.Rcpt.Extract.AcctProof
import ZkFormal.NearV3.Rcpt.Extract.AkeyProof
import ZkFormal.NearV3.Rcpt.Extract.BndProof
import ZkFormal.NearV3.Rcpt.Extract.SizeProof
import ZkFormal.NearV3.Rcpt.Extract.V.ViewProof
import ZkFormal.NearV3.Public.Prepared

/-!
# ZkFormal.NearV3.Assembly.ExtractV3 — the AIR-to-semantics link

This module fixes the fixed table indices of `nearAirV3` and derives `TableLocal`
for every table from `HoldsP` — the mechanical first step of `ExtractV3Stmt`
(v1's `tableLocal_of_holds`).  The per-table views (`node3_view`, `walk3_view`,
`head_view`, `val_view`, `uniq_view`, `ups_view`, `acctV3_view`, `akey_view`,
`bnd_view`, `size_view`) are proved elsewhere; `RcptV3ViewStmt` and the `Link`
joining them into `GoodV3` remain the open part of item 3 (see
`docs/zk-formal/STATUS-V3-ASSEMBLY.md`).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpec NearSpecV3

/-! ## Table indices of `nearAirV3` (matches `NearAir.lean`) -/

def T_SHA_T : Nat := 0
def T_SHA_R : Nat := 1
def T_NODE : Nat := 2
def T_HEAD : Nat := 3
def T_VAL : Nat := 4
def T_WALK : Nat := 5
def T_UNIQ : Nat := 6
def T_UPS : Nat := 7
def T_CHACHA : Nat := 8
def T_RNG : Nat := 9
def T_SHUF : Nat := 10
def T_CODEC : Nat := 11
def T_SSD : Nat := 12
def T_PROC : Nat := 13
def T_MEM : Nat := 14
def T_CMP : Nat := 15
def T_RCPT : Nat := 16
def T_ACCT : Nat := 17
def T_AKEY : Nat := 18
def T_BND : Nat := 19
def T_SRCP : Nat := 20
def T_SIZE : Nat := 21
def T_QV : Nat := 22
def T_MRK : Nat := 23
def T_SORT : Nat := 24

/-- `HoldsP` gives the local legality of the table at index `t`. -/
theorem tableLocal_of_holdsP {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (h : HoldsP AP pub tr) {t : Nat} {T : ZkFormal.Air.Table} (ht : AP.tables[t]? = some T) :
    ZkFormal.Near.TableLocal T tr t pub := by
  have hlt : t < AP.tables.length := by
    rcases Nat.lt_or_ge t AP.tables.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at ht; cases ht
  have hT : AP.tables[t] = T := by
    rw [List.getElem?_eq_getElem hlt] at ht; exact Option.some.inj ht
  obtain ⟨h1, h2⟩ := h.logBound t hlt
  refine ⟨h1, hT ▸ h2, ?_, ?_⟩
  · intro r hr e he; exact h.constr t hlt r hr e (hT ▸ he)
  · intro r hr i hi b hb; exact h.bits t hlt r hr i (hT ▸ hi) b hb

/-- The `nearAirV3` table list in positional form. -/
theorem nearTablesFull_eq : nearAirV3.tables =
    [shaTable, shaTable, ZkFormal.NearV3.NodeV3.tableU, {ZkFormal.NearV3.HeadV3.table with maxLog := 13},
     ZkFormal.NearV3.ValV3.table, {ZkFormal.NearV3.WalkV3.table with maxLog := 22}, ZkFormal.NearV3.Uniq.table,
     ZkFormal.NearV3.UpsV3.table,
     ZkFormal.Chacha.Table.table ZkFormal.NearV3.Sched.B_SCHACHA,
     ZkFormal.Chacha.Rng.Table.table ZkFormal.NearV3.Sched.B_SCHACHA ZkFormal.NearV3.Sched.B_SGEN,
     ZkFormal.Chacha.Shuffle.Table.table ZkFormal.NearV3.Sched.B_SSIN ZkFormal.NearV3.Sched.B_SSOUT
       ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN ZkFormal.NearV3.Sched.B_SSHUF,
     ZkFormal.NearV3.Sched.Codec.table, ZkFormal.NearV3.Sched.ScanDist.table,
     ZkFormal.NearV3.Sched.Proc.table, ZkFormal.NearV3.Sched.Mem.table,
     ZkFormal.NearV3.Sched.Cmp.table ZkFormal.NearV3.Sched.B_SCMP,
     ZkFormal.NearV3.RcptV3.table, ZkFormal.NearV3.AcctV3.table, ZkFormal.NearV3.AkeyV3.table,
     ZkFormal.NearV3.BndV3.table, ZkFormal.NearV3.SrcpV3.table, ZkFormal.NearV3.SizeV3.table,
     ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table,
     ZkFormal.NearV3.Candidates.MerklePublic.table, {ZkFormal.Near.Sort.table with maxLog := 18}] := rfl

/-- The `nearAirV3` table list is definitionally `nearTablesFull`; the index lemmas are
`rfl` on `NearAir.nearAirV3_tables`. -/
theorem tables_eq : nearAirV3.tables = nearAirV3Air.tables := rfl

/-! ## Per-index lookups (the interface the per-table views plug into) -/

theorem getElem?_node : nearAirV3.tables[T_NODE]? = some ZkFormal.NearV3.NodeV3.tableU := rfl
theorem getElem?_head : nearAirV3.tables[T_HEAD]? =
    some {ZkFormal.NearV3.HeadV3.table with maxLog := 13} := rfl
theorem getElem?_val : nearAirV3.tables[T_VAL]? = some ZkFormal.NearV3.ValV3.table := rfl
theorem getElem?_walk : nearAirV3.tables[T_WALK]? =
    some {ZkFormal.NearV3.WalkV3.table with maxLog := 22} := rfl
theorem getElem?_uniq : nearAirV3.tables[T_UNIQ]? = some ZkFormal.NearV3.Uniq.table := rfl
theorem getElem?_ups : nearAirV3.tables[T_UPS]? = some ZkFormal.NearV3.UpsV3.table := rfl
theorem getElem?_rcpt : nearAirV3.tables[T_RCPT]? = some ZkFormal.NearV3.RcptV3.table := rfl
theorem getElem?_acct : nearAirV3.tables[T_ACCT]? = some ZkFormal.NearV3.AcctV3.table := rfl
theorem getElem?_akey : nearAirV3.tables[T_AKEY]? = some ZkFormal.NearV3.AkeyV3.table := rfl
theorem getElem?_bnd : nearAirV3.tables[T_BND]? = some ZkFormal.NearV3.BndV3.table := rfl
theorem getElem?_srcp : nearAirV3.tables[T_SRCP]? = some ZkFormal.NearV3.SrcpV3.table := rfl
theorem getElem?_size : nearAirV3.tables[T_SIZE]? = some ZkFormal.NearV3.SizeV3.table := rfl
theorem getElem?_mrk : nearAirV3.tables[T_MRK]? =
    some ZkFormal.NearV3.Candidates.MerklePublic.table := rfl
theorem getElem?_sort : nearAirV3.tables[T_SORT]? =
    some {ZkFormal.Near.Sort.table with maxLog := 18} := rfl

/-! ## `TableLocal` of each table from `HoldsP` (the inputs the views consume) -/

variable {pub : List Fp} {tr : Trace Fp}

theorem nodeLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.NodeV3.tableU tr T_NODE pub :=
  tableLocal_of_holdsP h getElem?_node

theorem headLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal {ZkFormal.NearV3.HeadV3.table with maxLog := 13} tr T_HEAD pub :=
  tableLocal_of_holdsP h getElem?_head

theorem valLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.ValV3.table tr T_VAL pub :=
  tableLocal_of_holdsP h getElem?_val

theorem walkLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal {ZkFormal.NearV3.WalkV3.table with maxLog := 22} tr T_WALK pub :=
  tableLocal_of_holdsP h getElem?_walk

theorem uniqLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.Uniq.table tr T_UNIQ pub :=
  tableLocal_of_holdsP h getElem?_uniq

theorem upsLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.UpsV3.table tr T_UPS pub :=
  tableLocal_of_holdsP h getElem?_ups

theorem rcptLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.RcptV3.table tr T_RCPT pub :=
  tableLocal_of_holdsP h getElem?_rcpt

theorem acctLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.AcctV3.table tr T_ACCT pub :=
  tableLocal_of_holdsP h getElem?_acct

theorem akeyLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.AkeyV3.table tr T_AKEY pub :=
  tableLocal_of_holdsP h getElem?_akey

theorem bndLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.BndV3.table tr T_BND pub :=
  tableLocal_of_holdsP h getElem?_bnd

theorem srcpLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.SrcpV3.table tr T_SRCP pub :=
  tableLocal_of_holdsP h getElem?_srcp

theorem sizeLocal (h : HoldsP nearAirV3 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.SizeV3.table tr T_SIZE pub :=
  tableLocal_of_holdsP h getElem?_size

/-! ## The `rcptV3` view of the assembled AIR (item 2, `rcpt-view`) -/

/-- **`RcptV3ViewStmt` for `nearAirV3`**, from successful native preparation and the
packed public-size bound.  The receipts view is the exact traffic of the extracted
list view; `prepared_receipt_ranges` discharges the public-range premise from
`prepD0` (`Public.preparedBytes`, the concrete `nearAirV3.pubSegs`). -/
theorem rcptV3_view_nearAir {cb : Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsize : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (tr : Trace Fp) (t : Nat)
    (hL : ZkFormal.Near.TableLocal ZkFormal.NearV3.RcptV3.table tr t
      (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))) :
    ∃ ls, ZkFormal.NearV3.RcptV3Wf (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) ls ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.RcptV3.interactions tr t
        (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))
        (ZkFormal.NearV3.rcptTraffic3
          (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) ls) :=
  ZkFormal.NearV3.RcptV3Proof.extract_prepared_view hp oh hsize tr t hL

end ZkFormal.NearV3.Assembly
