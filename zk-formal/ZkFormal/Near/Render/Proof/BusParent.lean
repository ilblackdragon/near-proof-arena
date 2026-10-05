import ZkFormal.Near.Render.Proof.NodeViewFacts
import ZkFormal.Near.Render.Proof.BusCommon

/-!
# ZkFormal.Near.Render.Proof.BusParent — `ParentBusStmt` (under `KeyBound`)

`node` sends `PARENT (c, depth + 1, len c, res c)` for each revealed child `c`
of each node and receives `PARENT (n, depth n, len n, res n)` for each non-root
node `n`.  Every non-root node is the child of exactly one slot (`TreeShape`),
depths increase by one along child links, and the length the receiver states
(that of its view's serialization) is the generator's (`view_pre`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

namespace BusParent

theorem count_kidIds (a : Nat) : ∀ (l : List Kid),
    (l.filterMap fun k => match k with | .node c => some c | _ => none).count a = l.count (Kid.node a)
  | [] => rfl
  | k :: l => by
    cases k with
    | none => simp [List.filterMap_cons, count_kidIds a l]
    | hash h => simp [List.filterMap_cons, count_kidIds a l]
    | node c =>
      simp only [List.filterMap_cons, List.count_cons, count_kidIds a l]
      by_cases h : c = a <;> simp [h]

theorem count_children {ns : List NodeRec} (hs : TreeShape ns) (a : Nat) :
    ((List.range ns.length).flatMap fun n => kidIds (ns.toArray.getD n (.branch none [] 0))).count a =
      ((List.range ns.length).drop 1).count a := by
  rw [List.count_flatMap]
  have hterm : ∀ n, n < ns.length → (List.count a ∘ fun n => kidIds (ns.toArray.getD n (.branch none [] 0))) n =
      (ns[n]?.map fun nr => nr.kids.count (Kid.node a)).getD 0 := by
    intro n hn
    simp only [Function.comp_apply, NodeInfo.getD_arr (show ns[n]? = some ns[n] by simp [hn]),
      List.getElem?_eq_getElem hn, Option.map_some, Option.getD_some, kidIds]
    exact count_kidIds a _
  rw [List.map_congr_left (fun n hn => hterm n (List.mem_range.1 hn)), Sound.sum_range_getElem?]
  have hnd : ((List.range ns.length).drop 1).Nodup := (List.drop_sublist _ _).nodup List.nodup_range
  by_cases ha : 0 < a ∧ a < ns.length
  · rw [show (ns.map fun nr => nr.kids.count (Kid.node a)).sum = refCount ns a from rfl,
      hs.unique_parent a ha.1 ha.2, List.Nodup.count_of_mem hnd]
    rw [List.mem_iff_getElem]
    exact ⟨a - 1, by simp; omega, by simp; omega⟩
  · rw [List.count_eq_zero_of_not_mem (fun hm => ha (by
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
      simp at hi he; omega))]
    apply Nat.eq_zero_of_le_zero
    apply Nat.le_of_not_lt; intro hpos
    obtain ⟨nr, hnr, hp⟩ := Link.exists_pos_of_sum _ _ hpos
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hnr
    have := hs.child_range n a ⟨_, by simp [hn], List.count_pos_iff.1 hp⟩
    exact ha this

end BusParent

open BusParent NodeInfo in
/-- **`ParentBusStmt`** under `KeyBound`. -/
theorem parentBus' : ∀ (c : WfClaim) (e : Ext), Good c.1 e → KeyBound e →
    ∀ m, hcount c.1 e B_PARENT true m = hcount c.1 e B_PARENT false m := by
  intro c e hg hk m
  rw [hcount_eq, hcount_eq]
  simp only [sel, ite_true, Bool.false_eq_true, ite_false, shaTraffic, nodeTraffic, nodeSends, nodeRecvs,
    walkTraffic, walkRecvs, walkSends, rcptTraffic, rcptSends, rcptRecvs, acctTraffic, acctSends, acctRecvs,
    mrkTraffic, mrkSends, mrkRecvs, sortTraffic, B_VSLOT, B_DIGEST, B_BYTES, B_PARENT, B_EDGE, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_FINAL, Nat.reduceEqDiff, cnt_nil, Nat.zero_add, Nat.add_zero, bundle_info]
  have hs := hg.shape
  let F : Nat → List Nat := fun k => [k, (mkInfo c.1 e).depth.getD k 0, ((mkInfo c.1 e).pre.getD k []).length,
    (mkInfo c.1 e).res.getD k k]
  have hN : (mkInfo c.1 e).ns.size = e.ns.length := info_N
  have hsend : ((nodeViewsOf (mkInfo c.1 e) (edgeUses (bundle c.1 e).walks)).zip
      (List.range (nodeViewsOf (mkInfo c.1 e) (edgeUses (bundle c.1 e).walks)).length)).flatMap
        (fun x => x.1.v.revealed.map fun y => [y.1, x.1.depth + 1, y.2.1, y.2.2.1]) =
      ((List.range e.ns.length).flatMap fun n => kidIds (e.ns.toArray.getD n (.branch none [] 0))).map F := by
    simp only [nodeViewsOf, List.length_map, List.length_range, zip_range_map, List.flatMap_map, hN,
      List.map_flatMap]
    apply flatMap_congr'; intro n hn
    have hn' := List.mem_range.1 hn
    simp only [nodeViewOf, view_revealed, List.map_map, info_nodeAt hn',
      NodeInfo.getD_arr (show e.ns[n]? = some e.ns[n] by simp [hn'])]
    apply List.map_congr_left; intro k hk
    have hch : ChildOf e.ns n k := ⟨_, by simp [hn'], kidIds_mem.1 hk⟩
    simp only [Function.comp_apply, revOf, F, depth_child hs hch]
  have hrecv : (((nodeViewsOf (mkInfo c.1 e) (edgeUses (bundle c.1 e).walks)).zip
      (List.range (nodeViewsOf (mkInfo c.1 e) (edgeUses (bundle c.1 e).walks)).length)).drop 1).map
        (fun x => [x.2, x.1.depth, (x.1.v.ser false).length, x.1.res]) =
      ((List.range e.ns.length).drop 1).map F := by
    simp only [nodeViewsOf, List.length_map, List.length_range, zip_range_map, hN, ← List.map_drop,
      List.map_map]
    apply List.map_congr_left; intro n hn
    have hn' : n < e.ns.length := List.mem_range.1 ((List.drop_sublist _ _).subset hn)
    simp only [Function.comp_apply, nodeViewOf, F, info_nodeAt hn',
      view_pre hg hn' (hk _ (List.getElem_mem hn'))]
  rw [hsend, hrecv]
  exact ((List.perm_iff_count.2 (count_children hs)).map _ |>.map Msg.toFp).count_eq m

/-- `ParentBusStmt` from the missing `Good` field `KeyBound` (R-L6e-2). -/
theorem parentBus_of (h : ∀ (c : Claim) (e : Ext), Good c e → KeyBound e) : ParentBusStmt :=
  fun c e hg => parentBus' c e hg (h c.1 e hg)

end ZkFormal.Near.Render
