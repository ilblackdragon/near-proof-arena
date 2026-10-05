import ZkFormal.Near.Render.Compose
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

/-!
# ZkFormal.Near.Render.Proof.Main — what is left of `RenderStmt`

`render_of_rest : RenderRest → RenderStmt`: the proved obligations (sort,
acct, walk, mrk local + traffic; buses VSLOT, RIDS, MEM, FINAL, KEYNIB) are
plugged in; `RenderRest` lists the open ones, plus the missing `Good` field
`TouchedLe` (R-L6e-1, needed for the acct table's height bound).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

/-- The open render obligations. -/
structure RenderRest : Prop where
  /-- R-L6e-1: `Good` must bound the touched nodes -/
  touched : ∀ (c : Claim) (e : Ext), Good c e → TouchedLe e
  shaL : ShaLocalStmt
  nodeL : NodeLocalStmt
  rcptL : RcptLocalStmt
  shaT : ShaTrafficStmt
  nodeT : NodeTrafficStmt
  rcptT : RcptTrafficStmt
  bytes : BytesBusStmt
  digest : DigestBusStmt
  parent : ParentBusStmt
  edge : EdgeBusStmt
  mpos : MposBusStmt

/-- **`RenderStmt` from the open obligations.** -/
theorem render_of_rest (h : RenderRest) : RenderStmt :=
  render_stmt
    { shaL := h.shaL, nodeL := h.nodeL, walkL := walkLocal, rcptL := h.rcptL,
      acctL := acctLocal_of h.touched, mrkL := mrkLocal, sortL := sortLocal,
      shaT := h.shaT, nodeT := h.nodeT, walkT := walkTraffic_ok, rcptT := h.rcptT,
      acctT := acctTraffic_ok, mrkT := mrkTraffic_ok, sortT := sortTraffic_ok,
      bytes := h.bytes, digest := h.digest, parent := h.parent, vslot := vslotBus, edge := h.edge,
      keynib := keynibBus, final := finalBus, mem := memBus, rids := ridsBus, mpos := h.mpos }

end ZkFormal.Near.Render
