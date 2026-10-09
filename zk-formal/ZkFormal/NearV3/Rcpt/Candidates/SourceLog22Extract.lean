import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Local
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Carry
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountSourcePartitions

set_option maxRecDepth 32768
namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra
open DedupPartitionTable

/-- Arbitrary accepted middle traces recover every original source polynomial
with global-first disabled. This is a field soundness theorem, not an honest
renderer assumption or an invalid lift of field equality to integer equality. -/
theorem middle_logical_constraints {tr : Trace Fp} {tt r incoming outgoing : Nat}
    {pub : List Fp} (h : TableLocal (SizeCount.sourceTable (middleTable incoming outgoing)) tr tt pub)
    (hr : r<tr.height tt) (hl : r+1≠tr.height tt) :
    ∀ ex∈DedupTable.constraints,
      ex.evalWith {rowEnv tr tt r pub with isFirst := 0}=0 := by
  have hb := SizeCount.source_local_base h
  apply field_zero_first_of_right tr tt r pub
  intro ex hex
  rcases List.mem_append.mp hex with hex|hex
  · exact middle_constraint hb hr hl ex hex
  · have he : ex=rightEndpoint := by simpa using hex
    subst ex
    simp only [rightEndpoint,eval_mul,eval_isLast,hl,ite_false]
    grind

/-- The arity-three SIZE decoration cannot change carry authentication. -/
theorem counted_middle_carry_equal (tr : Trace Fp) (left right : Nat) (pub : List Fp)
    (h : ∀ m,
      tableBusCount (SizeCount.sourceTable (middleTable 64 65)).interactions tr left pub 65 true m =
      tableBusCount (SizeCount.sourceTable (middleTable 65 66)).interactions tr right pub 65 false m) :
    carryRow tr left (tr.height left-1)=carryRow tr right 0 := by
  apply middle_carry_equal tr left right pub
  intro m
  have hh := h m
  simp only [SizeCount.sourceTable,SizeCount.count_nonSize _ _ 65 (by decide)] at hh
  exact hh

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
