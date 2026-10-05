import ZkFormal.Near.Render.Compose
import ZkFormal.Near.Compose
import ZkFormal.Near.Spec.SmallComplete
import ZkFormal.Near.Render.Proof.SortLocal
import ZkFormal.Near.Render.Proof.SortTraffic
import ZkFormal.Near.Render.Proof.AcctLocal
import ZkFormal.Near.Render.Proof.AcctTraffic
import ZkFormal.Near.Render.Proof.WalkLocal
import ZkFormal.Near.Render.Proof.WalkTraffic
import ZkFormal.Near.Render.Proof.MrkLocal4
import ZkFormal.Near.Render.Proof.MrkTraffic3
import ZkFormal.Near.Render.Proof.BusVslot
import ZkFormal.Near.Render.Proof.BusRids
import ZkFormal.Near.Render.Proof.BusMem
import ZkFormal.Near.Render.Proof.BusFinal
import ZkFormal.Near.Render.Proof.BusMpos
import ZkFormal.Near.Render.Proof.ShaFit4
import ZkFormal.Near.Render.Proof.RcptBytes2
import ZkFormal.Near.Render.Proof.RcptLocal

/-!
# ZkFormal.Near.Render.Proof.Main — what is left of `RenderStmt`

`render_of_rest : RenderRest → RenderStmt`: the proved obligations (sha,
sort, acct, walk, mrk local + traffic; BYTES given `NodeSerStmt`; buses VSLOT, RIDS, MEM, FINAL, KEYNIB, MPOS) are
plugged in; `RenderRest` lists the open ones.  All obligations are stated
under `Good c.1 e ∧ Small e` (R-L6e-1 resolved: the acct table's height bound
comes from `Small.touched`).

`nearAir_complete_rest` / `honestTrace_fits_rest`: the DESIGN completeness
statements from `RenderRest` alone (`good_complete`, `small_complete`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- The open render obligations. -/
structure RenderRest : Prop where
  nodeL : NodeLocalStmt
  /-- the open `rcpt` constraint families (`RcptLocalStmt` = `RcptP.rcptLocal_fams`) -/
  rcptL : RcptP.RcptFams
  nodeT : NodeTrafficStmt
  rcptT : RcptTrafficStmt
  /-- the node views serialize as `mkInfo`'s `pre`/`post` (gives `BytesBusStmt` via `bytesBus_of`) -/
  nodeSer : NodeSerStmt
  digest : DigestBusStmt
  parent : ParentBusStmt
  edge : EdgeBusStmt

/-- **`RenderStmt` from the open obligations.** -/
theorem render_of_rest (h : RenderRest) : RenderStmt :=
  render_stmt
    { shaL := shaLocal, nodeL := h.nodeL, walkL := walkLocal, rcptL := RcptP.rcptLocal_fams h.rcptL,
      acctL := acctLocal, mrkL := mrkLocal, sortL := sortLocal,
      shaT := shaTraffic_ok, nodeT := h.nodeT, walkT := walkTraffic_ok, rcptT := h.rcptT,
      acctT := acctTraffic_ok, mrkT := mrkTraffic_ok, sortT := sortTraffic_ok,
      bytes := bytesBus_of h.nodeSer rcptBytes, digest := h.digest, parent := h.parent, vslot := vslotBus, edge := h.edge,
      keynib := keynibBus, final := finalBus, mem := memBus, rids := ridsBus, mpos := mposBus }

/-- **Completeness of the NEAR AIR** from the open render obligations. -/
theorem nearAir_complete_rest (h : RenderRest) :
    ∀ (c : WfClaim) (w : Witness), NearRelation c.1 w → Holds nearAir (publicOf c) (honestTrace c w) :=
  nearAir_complete good_complete small_complete (render_of_rest h)

/-- **The honest trace fits** every table's height bound. -/
theorem honestTrace_fits_rest (h : RenderRest) {c : WfClaim} {w : Witness} (hr : NearRelation c.1 w) :
    ∀ t (ht : t < nearAir.tables.length),
      1 ≤ (honestTrace c w).log t ∧ (honestTrace c w).log t ≤ nearAir.tables[t].maxLog :=
  honestTrace_fits good_complete small_complete (render_of_rest h) hr

end ZkFormal.Near.Render
