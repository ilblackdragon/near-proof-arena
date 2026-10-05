import ZkFormal.Near.Render.Proof.BusCommon

/-!
# ZkFormal.Near.Render.Proof.BusVslot — `VslotBusStmt`

`acct` offers each touched slot once, `node` takes each touched node once.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

theorem nodeVOf_touched (I : Info) (n : Nat) (nr : NodeRec) : (nodeVOf I n nr).touched = nr.touched := by
  cases nr with
  | leaf k v mem => cases v <;> rfl
  | ext k kid mem => rfl
  | branch v kids mem =>
    rcases v with _ | v
    · rfl
    · cases v <;> rfl

/-- **`VslotBusStmt`.** -/
theorem vslotBus : VslotBusStmt := by
  intro c e _ _ m
  rw [hcount_eq, hcount_eq]
  simp only [sel, if_true, Bool.false_eq_true, if_false, shaTraffic, nodeTraffic, nodeSends, nodeRecvs,
    walkTraffic, walkSends, walkRecvs, rcptTraffic, rcptSends, rcptRecvs, acctTraffic, acctSends, acctRecvs,
    mrkTraffic, mrkSends, mrkRecvs, sortTraffic, B_VSLOT, B_DIGEST, B_BYTES, B_PARENT, B_EDGE, B_KEYNIB,
    B_FINAL, B_MEM, B_RIDS, B_MPOS, Nat.reduceEqDiff, cnt_nil, Nat.zero_add, Nat.add_zero, bundle_info]
  congr 1
  simp only [acctViewsOf, List.map_map, nodeViewsOf, zip_range_map, List.length_map, List.length_range,
    List.filterMap_map]
  rw [mkInfo_touched]
  have : (mkInfo c.1 e).ns.size = e.ns.length := by simp [mkInfo]
  rw [this, map_filter_eq]
  congr 1; funext x
  simp only [Function.comp_apply]
  have hv : (nodeViewOf (mkInfo c.1 e) (edgeUses (bundle c.1 e).walks) x).v.touched =
      (e.ns.toArray.getD x (NodeRec.branch none [] 0)).touched := by
    simp only [nodeViewOf]; exact nodeVOf_touched _ _ _
  rw [hv]

end ZkFormal.Near.Render
