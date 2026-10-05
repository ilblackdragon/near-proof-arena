import ZkFormal.Near.Render.Proof.BusCommon
import ZkFormal.Near.Render.Proof.SortIds

/-!
# ZkFormal.Near.Render.Proof.BusRids — `RidsBusStmt`

`rcpt` sends the 32 id bytes of every receipt (receipt order), `sort`
receives them in sorted order: a permutation.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

theorem zip_range_getD {α : Type} (d : α) (l : List α) :
    l.zip (List.range l.length) = (List.range l.length).map fun r => (l.getD r d, r) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp at h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem cnt_perm {l₁ l₂ : List ZkFormal.Near.Msg} (h : l₁.Perm l₂) (m : List Fp) : cnt l₁ m = cnt l₂ m :=
  (h.map Msg.toFp).count_eq m

/-- **`RidsBusStmt`.** -/
theorem ridsBus : RidsBusStmt := by
  intro c e _ m
  rw [hcount_eq, hcount_eq]
  simp only [sel, if_true, Bool.false_eq_true, if_false, shaTraffic, nodeTraffic, nodeSends, nodeRecvs,
    walkTraffic, walkSends, walkRecvs, rcptTraffic, rcptSends, rcptRecvs, acctTraffic, acctSends, acctRecvs,
    mrkTraffic, mrkSends, mrkRecvs, sortTraffic, B_VSLOT, B_DIGEST, B_BYTES, B_PARENT, B_EDGE, B_KEYNIB,
    B_FINAL, B_MEM, B_RIDS, B_MPOS, Nat.reduceEqDiff, cnt_nil, Nat.zero_add, Nat.add_zero, bundle_info]
  apply cnt_perm
  simp only [sortIdsOf, sortedIds]
  refine List.Perm.trans ?_ ((perm_sorted (rawIds (mkInfo c.1 e))).flatMap_right _).symm
  apply List.Perm.of_eq
  simp only [rcptViewsOf, rcptData, rawIds, List.map_map, List.length_map, List.length_range,
    zip_range_map, mkInfo_e]
  rw [zip_range_getD ⟨[], [], [], [], ⟨0, []⟩, 0, 0⟩ e.rs]
  simp only [List.flatMap_map]
  rfl

end ZkFormal.Near.Render
