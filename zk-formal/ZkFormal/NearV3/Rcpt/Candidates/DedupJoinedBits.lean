import ZkFormal.NearV3.Rcpt.Candidates.DedupJoinedTrace

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

private def baseSelectors : List Expr := [SrcpV3.sg, SrcpV3.gD, SrcpV3.rt, SrcpV3.gz].map Dsl.c

set_option maxRecDepth 8192 in
private theorem selector_mem : ∀ i ∈ DedupTable.interactions,
    ∀ e ∈ i.mult, e ∈ baseSelectors := by
  have hh : DedupTable.interactions.all
      (fun i => i.mult.all (fun e => baseSelectors.any (fun b => decide (e=b)))) = true := by
    decide +kernel
  intro i hi e he
  obtain ⟨b, hb, heq⟩ := List.any_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp hh i hi) e he)
  exact (of_decide_eq_true heq).symm ▸ hb

/-- Base multiplicities read only the current row, so physical row relocation
preserves their field values. -/
theorem base_mult_current {tr tr' : Trace Fp} {t r t' r' : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell t r x=tr'.cell t' r' x) :
    ∀ i ∈ DedupTable.interactions, ∀ b ∈ i.mult,
      b.eval tr t r pub=b.eval tr' t' r' pub := by
  intro i hi b hb
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp (selector_mem i hi b hb)
  exact hc x

/-- Suppressed left carry traffic does not lose bit checks on retained rows. -/
theorem base_bits_of_left {tr : Trace Fp} {t r carryBus : Nat} {pub : List Fp}
    (hl : r+1≠tr.height t)
    (h : ∀ i ∈ leftInteractions carryBus, ∀ b ∈ i.mult,
      b.eval tr t r pub=0 ∨ b.eval tr t r pub=1) :
    ∀ i ∈ DedupTable.interactions, ∀ b ∈ i.mult,
      b.eval tr t r pub=0 ∨ b.eval tr t r pub=1 := by
  intro i hi b hb
  have hh := h { i with mult := i.mult.map fun e => .mul (Dsl.not .isLast) e }
    (List.mem_append_left _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
    (.mul (Dsl.not .isLast) b) (List.mem_map.mpr ⟨b, hb, rfl⟩)
  simp only [eval_mul, eval_not, eval_isLast, hl, ite_false] at hh
  grind

/-- All logical multiplicity digits are bits after joining the partitions,
including the final cloned padding row. -/
theorem joined_trace_bits {tr : Trace Fp} {left right carryBus : Nat} {pub : List Fp}
    (hleft : TableLocal (leftTable carryBus) tr left pub)
    (hright : TableLocal (rightTable carryBus) tr right pub)
    (hheight : tr.height right=tr.height left) :
    ∀ r, r<(joinedTrace tr left right).height 0 →
      ∀ i ∈ DedupTable.interactions, ∀ b ∈ i.mult,
        b.eval (joinedTrace tr left right) 0 r pub=0 ∨
        b.eval (joinedTrace tr left right) 0 r pub=1 := by
  intro r hr i hi b hb
  by_cases hl : r<tr.height left-1
  · rw [base_mult_current (tr' := tr) (t' := left) (r' := r)
      (fun x => congrFun (joined_left (tr.height left) (tr.cell left) (tr.cell right) hl) x) i hi b hb]
    exact base_bits_of_left (by omega) (hleft.bits r (by omega)) i hi b hb
  · let q := min (r-(tr.height left-1)) (tr.height left-1)
    have hq : q<tr.height right := by
      have hm : q≤tr.height left-1 := Nat.min_le_right _ _
      have hp := Nat.two_pow_pos (tr.log left)
      change 0<tr.height left at hp
      omega
    rw [base_mult_current (tr' := tr) (t' := right) (r' := q)
      (fun x => by simp only [joinedTrace, joinedCells, hl, ite_false]; rfl) i hi b hb]
    exact hright.bits q hq i (List.mem_append_left _ hi) b hb

/-- Both physical local predicates and carry equality reconstruct a complete
logical source TableLocal at log≤24, without assuming honest source cells. -/
theorem joined_table_local {tr : Trace Fp} {left right carryBus : Nat} {pub : List Fp}
    (hleft : TableLocal (leftTable carryBus) tr left pub)
    (hright : TableLocal (rightTable carryBus) tr right pub)
    (hheight : tr.height right=tr.height left)
    (hcarry : ∀ x, x<57 → tr.cell left (tr.height left-1) x=tr.cell right 0 x) :
    TableLocal (DedupTable.table 24) (joinedTrace tr left right) 0 pub := by
  refine ⟨?_, ?_, joined_trace_constraints hleft hright hheight hcarry,
    joined_trace_bits hleft hright hheight⟩
  · change 1≤tr.log left+1; omega
  · have hh := hleft.log_le
    change tr.log left≤23 at hh
    change tr.log left+1≤24
    omega

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
