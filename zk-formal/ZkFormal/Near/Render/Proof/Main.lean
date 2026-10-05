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
import ZkFormal.Near.Render.Proof.BusEdge
import ZkFormal.Near.Render.Proof.BusParent
import ZkFormal.Near.Render.Proof.NodeSer
import ZkFormal.Near.Render.Proof.NodeTraffic
import ZkFormal.Near.Render.Proof.RcptTraffic
import ZkFormal.Near.Render.Proof.BusDigest
import ZkFormal.Near.Render.Proof.NodeLocal

/-!
# ZkFormal.Near.Render.Proof.Main — `RenderStmt`, closed

Every render obligation is proved (sha, node, walk, rcpt, acct, mrk, sort:
local + traffic; buses BYTES, DIGEST, PARENT, VSLOT, EDGE, KEYNIB, FINAL,
MEM, RIDS, MPOS), all under `Good c.1 e ∧ Small e`.

* `render_stmt_closed : RenderStmt`;
* `nearAir_complete_closed` / `honestTrace_fits_closed`: the DESIGN
  completeness statements, hypothesis-free (`good_complete`, `small_complete`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- **`RenderStmt`**: the honest trace of `Good ∧ Small` records satisfies the NEAR AIR. -/
theorem render_stmt_closed : RenderStmt :=
  render_stmt
    { shaL := shaLocal, nodeL := nodeLocal, walkL := walkLocal, rcptL := RcptP.rcptLocal,
      acctL := acctLocal, mrkL := mrkLocal, sortL := sortLocal,
      shaT := shaTraffic_ok, nodeT := nodeTraffic_ok, walkT := walkTraffic_ok, rcptT := RcptP.rcptTraffic_ok,
      acctT := acctTraffic_ok, mrkT := mrkTraffic_ok, sortT := sortTraffic_ok,
      bytes := bytesBus_of nodeSer_ok rcptBytes, digest := digestBus, parent := parentBus,
      vslot := vslotBus, edge := edgeBus,
      keynib := keynibBus, final := finalBus, mem := memBus, rids := ridsBus, mpos := mposBus }

/-- **Completeness of the NEAR AIR.** -/
theorem nearAir_complete_closed :
    ∀ (c : WfClaim) (w : Witness), NearRelation c.1 w → Holds nearAir (publicOf c) (honestTrace c w) :=
  nearAir_complete good_complete small_complete render_stmt_closed

/-- **The honest trace fits** every table's height bound. -/
theorem honestTrace_fits_closed {c : WfClaim} {w : Witness} (hr : NearRelation c.1 w) :
    ∀ t (ht : t < nearAir.tables.length),
      1 ≤ (honestTrace c w).log t ∧ (honestTrace c w).log t ≤ nearAir.tables[t].maxLog :=
  honestTrace_fits good_complete small_complete render_stmt_closed hr

end ZkFormal.Near.Render
