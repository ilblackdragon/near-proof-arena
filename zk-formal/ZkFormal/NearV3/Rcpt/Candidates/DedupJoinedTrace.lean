import ZkFormal.NearV3.Rcpt.Candidates.DedupJoinedConstraints

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- A logical source trace reconstructed from a physical partition pair. -/
def joinedTrace (tr : Trace Fp) (left right : Nat) : Trace Fp :=
  { log := fun _ => tr.log left + 1,
    cell := fun _ => joinedCells (tr.height left) (tr.cell left) (tr.cell right) }

theorem joined_height (tr : Trace Fp) (left right tt : Nat) :
    (joinedTrace tr left right).height tt = 2 * tr.height left := by
  simp [Trace.height, joinedTrace, Nat.pow_succ, Nat.mul_comm]

/-- Direct field constraints for the reconstructed logical trace follow from the
two physical local predicates and authenticated overlap equality. -/
theorem joined_trace_constraints {tr : Trace Fp} {left right carryBus : Nat} {pub : List Fp}
    (hleft : TableLocal (leftTable carryBus) tr left pub)
    (hright : TableLocal (rightTable carryBus) tr right pub)
    (hheight : tr.height right = tr.height left)
    (hcarry : ∀ x, x<57 → tr.cell left (tr.height left-1) x=tr.cell right 0 x) :
    ∀ r, r<(joinedTrace tr left right).height 0 →
      ∀ e ∈ DedupTable.constraints, e.eval (joinedTrace tr left right) 0 r pub = 0 := by
  have hH : 2≤tr.height left := by
    have hp := Nat.pow_le_pow_right (by decide : 1≤2) hleft.log_ge
    simpa only [Nat.pow_one, Trace.height] using hp
  have hL : ∀ r, r<tr.height left-1 →
      SourceRow (tr.cell left r) (tr.cell left (r+1)) (if r=0 then 1 else 0) 0 1
        (fun i => pub.getD i 0) := by
    intro r hr
    have hn : r+1≠tr.height left := by omega
    have hm : (r+1)%tr.height left=r+1 := Nat.mod_eq_of_lt (by omega)
    have hh := field_base_of_left hn (hleft.constr r (by omega))
    simp only [Expr.eval, rowEnv_cellEnv, hn, ite_false, hm] at hh
    exact hh
  have hR : ∀ r, r<tr.height left →
      SourceRow (tr.cell right r) (tr.cell right ((r+1)%tr.height left)) 0
        (if r+1=tr.height left then 1 else 0) (if r+1=tr.height left then 0 else 1)
        (fun i => pub.getD i 0) := by
    intro r hr
    have hh := field_zero_first_of_right tr right r pub
      (hright.constr r (by omega))
    rw [rowEnv_cellEnv] at hh
    simpa only [hheight, SourceRow, cellEnv] using hh
  have hI : Inactive (tr.cell right (tr.height left-1)) := by
    apply endpoint_inactive (pub := pub) (by omega)
    exact hright.constr _ (by omega)
  have hj := joined_constraints (tr.height left) hH (tr.cell left) (tr.cell right)
    (fun i => pub.getD i 0) hL hR hcarry hI
  intro r hr e he
  have hh := hj r (by simpa only [joined_height] using hr) e he
  simp only [Expr.eval, rowEnv_cellEnv, joined_height]
  exact hh

/-- Ideal carry-bus balance supplies exactly the overlap equality used by the
reconstruction. Integrated cryptographic bus soundness must supply this premise. -/
theorem joined_constraints_of_balance {tr : Trace Fp} {left right : Nat} {pub : List Fp}
    (hleft : TableLocal (leftTable sourceCarryBus) tr left pub)
    (hright : TableLocal (rightTable sourceCarryBus) tr right pub)
    (hheight : tr.height right = tr.height left)
    (hbal : ∀ m,
      tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus true m +
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus true m =
      tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus false m +
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus false m) :
    ∀ r, r<(joinedTrace tr left right).height 0 →
      ∀ e ∈ DedupTable.constraints, e.eval (joinedTrace tr left right) 0 r pub = 0 :=
  joined_trace_constraints hleft hright hheight
    (carry_cells tr left right (carry_equal_of_balance tr left right pub hbal))

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
