import ZkFormal.NearV3.Rcpt.Candidates.SizeCountDecorate
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountViews

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl

def nodePayload (vs : List NodeS3) : Nat :=
  ((vs.filter fun v => !v.dup).map fun v => (v.v.ser false).length).sum

/-- Actual candidate node sender supplies exactly one SIZE record containing the
payload and record count of the SAME extracted node view. -/
theorem node_size_sender {tr : Trace Fp} {pub : List Fp}
    (h : TableLocal nodeTable tr T_NODE pub) {segs : List (Nat×Nat)}
    (hs : NodeProof3.NodeSegs tr segs) :
    (List.range (tr.height T_NODE)).flatMap (fun r =>
      rowTraffic nodeTable.interactions tr T_NODE r pub B_SIZE true) =
      [[0,(nodePayload (NodeProof3.viewOf tr pub segs):Fp),
        (((NodeProof3.viewOf tr pub segs).filter fun v => !v.dup).length:Fp)]] := by
  have hl : TableLocal NodeV3.table tr T_NODE pub := node_local_base h
  have hr := hs.sumRow hl
  have hc := node_count_view h hs
  have hcf : tr.cell T_NODE (segEnd 0 segs) nodeCount =
      (((NodeProof3.viewOf tr pub segs).filter fun v => !v.dup).length:Fp) := by
    rw [←hc]; exact (Fp.ofNat_toNat _).symm
  have hone : NodeProof3.rowT tr pub (segEnd 0 segs) B_SIZE true=
      [[0,(NodeProof3.sizeOf tr segs:Fp)]] := by
    rw [NodeProof3.rowT_sizeS,hr.2.1,hs.szSum hl]
    simp [NodeProof3.gate]
  have hx := decorate_singleton (List.range (tr.height T_NODE))
    (fun r => NodeProof3.rowT tr pub r B_SIZE true)
    (fun r msg => msg++[tr.cell T_NODE r nodeCount]) (segEnd 0 segs)
    [0,(NodeProof3.sizeOf tr segs:Fp)] (List.mem_range.mpr hr.1) hone
    (NodeProof3.rowsSize hl hs)
  simp only [nodeTable,rowTraffic_withCount,ite_true,eval_c]
  change (List.range (tr.height T_NODE)).flatMap
    (fun r => (NodeProof3.rowT tr pub r B_SIZE true).map
      (fun msg => msg++[tr.cell T_NODE r nodeCount])) = _
  rw [hx,hcf]
  have hp := NodeProof3.viewOf_size hl hs
  change nodePayload (NodeProof3.viewOf tr pub segs)=NodeProof3.sizeOf tr segs at hp
  rw [hp]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
