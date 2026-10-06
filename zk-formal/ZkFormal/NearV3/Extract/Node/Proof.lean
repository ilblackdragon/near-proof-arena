import ZkFormal.NearV3.Extract.Node.WfProof

/-!
# ZkFormal.NearV3.Extract.Node.Proof — `node3_view : NodeV3ViewStmt`

The extraction is carried out at the fixed table index `T_NODE`; any table index `t` is
reduced to it by focusing the trace on table `t` (row environments, hence constraint
values and bus traffic, are definitionally unchanged).
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {segs : List (Nat × Nat)}

theorem nodeWfOf (hS : NodeSegs tr segs) : NodeWf3 (viewOf tr pub segs) := by
  have hlen : (viewOf tr pub segs).length = segs.length := by simp [viewOf]
  have hget : ∀ n (hn : n < (viewOf tr pub segs).length),
      (viewOf tr pub segs)[n] = nodeSOf tr pub segs[n].1 segs[n].2 := by
    intro n hn; simp [viewOf]
  have hH := hS.lenLt hL
  have hHP : tr.height T_NODE < P := by have := height_le hL; unfold P; omega
  have mem : ∀ S ∈ viewOf tr pub segs, ∃ p ∈ segs, S = nodeSOf tr pub p.1 p.2 := by
    intro S hS'; simp only [viewOf, List.mem_map] at hS'; obtain ⟨p, hp, rfl⟩ := hS'; exact ⟨p, hp, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS'; obtain ⟨p, hp, rfl⟩ := mem S hS'
    obtain ⟨fl, hC⟩ := hS.ctx hL hp
    exact (nodeV_wf hL hC).1
  · intro S hS'; obtain ⟨p, hp, rfl⟩ := mem S hS'
    obtain ⟨fl, hC⟩ := hS.ctx hL hp
    exact depthBound hL hC
  · intro n hn
    rw [hget]
    obtain ⟨fl, hC⟩ := hS.ctx hL (List.getElem_mem (show n < segs.length by omega))
    exact resOkNode hL hC (hS.nid hL n (by omega)) (by omega)
  · intro n hn
    rw [hget]
    obtain ⟨fl, hC⟩ := hS.ctx hL (List.getElem_mem (show n < segs.length by omega))
    exact usesLen hL hC (hS.nid hL n (by omega)) (by omega)
  · intro S hS'; obtain ⟨p, hp, rfl⟩ := mem S hS'
    exact ⟨cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, uses_lt tr pub p.1 p.2⟩
  · intro S hS'; obtain ⟨p, hp, rfl⟩ := mem S hS'
    obtain ⟨fl, hC⟩ := hS.ctx hL hp
    exact (nodeV_wf hL hC).2
  · rw [hlen]; have := height_le hL; omega
  · have hsum : ((viewOf tr pub segs).map fun s => (s.v.ser false).length).sum = segEnd 0 segs := by
      have gen : ∀ (l : List (Nat × Nat)) (s0 : Nat), Consec s0 l → (∀ p ∈ l, p ∈ segs) →
          ((l.map fun p => nodeSOf tr pub p.1 p.2).map fun s => (s.v.ser false).length).sum + s0 = segEnd s0 l := by
        intro l; induction l with
        | nil => intro s0 _ _; simp [segEnd]
        | cons p rest ih =>
          intro s0 hc hm
          obtain ⟨a, b'⟩ := p
          obtain ⟨rfl, hc'⟩ := hc
          obtain ⟨fl, hC⟩ := hS.ctx hL (hm (a, b') (by simp))
          have e := ih (a + b') hc' (fun q hq => hm q (by simp [hq]))
          simp only [List.map_cons, List.sum_cons, segEnd] at e ⊢
          rw [← e, show (nodeSOf tr pub a b').v = nodeVOf tr a from rfl, ← (nodeSer hL hC).1, rowsB_length]
          omega
      have := gen segs 0 hS.consec (fun p hp => hp)
      simp only [viewOf, List.map_map] at this ⊢
      simpa using this
    have := (hS.sumRow hL).1
    have := height_le hL
    omega

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Table `t` of `tr`, placed at every index. -/
def focusTr (tr : Trace Fp) (t : Nat) : Trace Fp := ⟨fun _ => tr.log t, fun _ => tr.cell t⟩

/-- **The `nodeV3` table extracts** (any table index). -/
theorem node3_view : NodeV3ViewStmt := by
  intro tr pub t hL
  have hL' : TableLocal NodeV3.table (focusTr tr t) T_NODE pub := ⟨hL.log_ge, hL.log_le, hL.constr, hL.bits⟩
  obtain ⟨segs, hS⟩ := NodeProof3.nodeSegs_exist hL'
  exact ⟨NodeProof3.viewOf (focusTr tr t) pub segs, NodeProof3.nodeWfOf hL' hS, NodeProof3.nodeTrafficOf hL' hS⟩

end ZkFormal.NearV3
