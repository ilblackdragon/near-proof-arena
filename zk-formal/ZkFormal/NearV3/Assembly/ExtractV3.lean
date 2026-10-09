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

/-- The `nearAirV3` table list is definitionally `nearTablesFull`; the index lemmas are
`rfl` on `NearAir.nearAirV3_tables`. -/
theorem tables_eq : nearAirV3.tables = nearAirV3Air.tables := rfl

end ZkFormal.NearV3.Assembly
