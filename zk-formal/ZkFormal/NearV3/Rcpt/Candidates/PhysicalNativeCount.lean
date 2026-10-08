import ZkFormal.NearV3.Rcpt.Candidates.NativeCountOwnership
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountViews

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near ZkFormal.Algebra NearSpec NearSpecV3 Link3 Assembly

/-- Retained native records are charged by the actual physical prefixes of the
same node/value views. Transition tags and empty values remain significant. -/
theorem native_count_from_physical_prefixes (k : WalkD0) (x : ExtV3)
    {us : List UniqE} {others : List Msg} {shaS shaR : Nat → List Fp → Nat}
    (hw : NodeWf3 x.nodes) (hhw : HeadWf x.heads) (hvw : ValWf x.values) (huw : UniqWf us)
    (hb : ParentBal x.nodes x.heads) (hvb : VParentBal x.nodes x.values)
    (H : ShaHyp x.nodes x.heads x.values others shaS shaR)
    (hD : DigsBal x.nodes x.heads us) (hDup : DupBal us x.nodes x.values)
    (hEnt : EntBal x.nodes x.values)
    (hheads : ∀ tau,tau≤k.implicitBlks.length → ∃ h∈x.heads,h.tau=tau)
    {tr : ZkFormal.Air.Trace Fp} {pub : List Fp} {tv : Nat}
    (hn : TableLocal SizeCount.nodeTable tr T_NODE pub)
    (hv : TableLocal SizeCount.valTable tr tv pub)
    (ns vs : List (Nat×Nat)) (hns : NodeProof3.NodeSegs tr ns)
    (hvc : Consec 0 vs) (hve : segEnd 0 vs<tr.height tv)
    (hvs : ∀ p∈vs, IsSeg (ValProof.isOne tr tv ValV3.act)
      (ValProof.isOne tr tv ValV3.vf) (ValProof.isOne tr tv ValV3.vl) p.1 p.2)
    (hxn : x.nodes=NodeProof3.viewOf tr pub ns)
    (hxv : x.values=vs.map (ValProof.valOf tr tv)) :
    witnessRecordCount (stateWitnessOfV3 k x)≤
      (tr.cell T_NODE (segEnd 0 ns) SizeCount.nodeCount).toNat+
      (tr.cell tv (segEnd 0 vs) SizeCount.valCount).toNat := by
  have hh := native_count_from_uniqueness k x hw hhw hvw huw hb hvb H hD hDup hEnt hheads
  rw [hxn,hxv] at hh
  rw [SizeCount.node_count_view hn hns,SizeCount.val_count_view hv vs hvc hve hvs]
  exact hh

end ZkFormal.NearV3.Rcpt.Candidates
