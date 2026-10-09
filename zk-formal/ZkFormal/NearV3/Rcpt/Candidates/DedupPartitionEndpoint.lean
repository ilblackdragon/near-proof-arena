import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionConstraintTransfer

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

set_option maxRecDepth 32768 in
private theorem disjoint_mem : (.mul (Dsl.c SrcpV3.rt) (Dsl.c SrcpV3.sg)) ∈ rightConstraints := by
  have hh : rightConstraints.any (fun e => decide (e = (.mul (Dsl.c SrcpV3.rt) (Dsl.c SrcpV3.sg)))) = true := by
    decide +kernel
  obtain ⟨e, he, heq⟩ := List.any_eq_true.mp hh
  exact (of_decide_eq_true heq) ▸ he

/-- The endpoint repair forces both activity flags individually to zero in the
actual base field, rather than relying on cancellation in their sum. -/
theorem field_endpoint_inactive {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (hl : r + 1 = tr.height tt)
    (h : ∀ ex ∈ rightConstraints, ex.eval tr tt r pub = 0) :
    tr.cell tt r SrcpV3.rt = 0 ∧ tr.cell tt r SrcpV3.sg = 0 := by
  have hs := field_endpoint_sum hl h
  have hd := h _ disjoint_mem
  simp only [eval_mul, eval_c] at hd
  rcases mul_eq_zero'.mp hd with hz | hz <;> grind

/-- In particular no active segment can cross the right cyclic boundary through
an authenticated carry row. This property holds for arbitrary accepting traces. -/
theorem local_endpoint_inactive {tr : Trace Fp} {tt carryBus : Nat} {pub : List Fp}
    (h : TableLocal (rightTable carryBus) tr tt pub) :
    tr.cell tt (tr.height tt - 1) SrcpV3.rt = 0 ∧
    tr.cell tt (tr.height tt - 1) SrcpV3.sg = 0 := by
  have hp : 0 < tr.height tt := Nat.two_pow_pos _
  apply field_endpoint_inactive (pub := pub) (by omega)
  exact h.constr _ (by omega)

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
