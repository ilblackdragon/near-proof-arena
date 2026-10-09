import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22HonestCarry

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open DedupPartitionTable

/-- Actual four-provider multiplicity on a named bus. The surrounding AIR must
isolate this sum from unrelated tables/public segments before applying the result. -/
def boundaryCount (tr : Trace Fp) (t0 t1 t2 t3 : Nat) (pub : List Fp)
    (b : Nat) (sd : Bool) (m : List Fp) : Nat :=
  tableBusCount (SizeCount.sourceTable firstTable).interactions tr t0 pub b sd m +
  tableBusCount (SizeCount.sourceTable (middleTable 64 65)).interactions tr t1 pub b sd m +
  tableBusCount (SizeCount.sourceTable (middleTable 65 66)).interactions tr t2 pub b sd m +
  tableBusCount (SizeCount.sourceTable lastTable).interactions tr t3 pub b sd m

/-- Every reserved bus has exactly its designated endpoints. This is a statement
about arbitrary trace cells, not about an honest renderer or local validity. -/
theorem boundary_count_exact (tr : Trace Fp) (t0 t1 t2 t3 : Nat) (pub : List Fp)
    (b : Nat) (hb : 64≤b) (sd : Bool) (m : List Fp) :
    boundaryCount tr t0 t1 t2 t3 pub b sd m=
      (if sd then
        (if b=64 then [carryRow tr t0 (tr.height t0-1)] else []) ++
        (if b=65 then [carryRow tr t1 (tr.height t1-1)] else []) ++
        (if b=66 then [carryRow tr t2 (tr.height t2-1)] else [])
      else
        (if b=64 then [carryRow tr t1 0] else []) ++
        (if b=65 then [carryRow tr t2 0] else []) ++
        (if b=66 then [carryRow tr t3 0] else [])).count m := by
  unfold boundaryCount
  simp only [tableBusCount_eq]
  change ((physicalMessages (SizeCount.sourceTable firstTable) tr t0 pub b sd).count m+
    (physicalMessages (SizeCount.sourceTable (middleTable 64 65)) tr t1 pub b sd).count m+
    (physicalMessages (SizeCount.sourceTable (middleTable 65 66)) tr t2 pub b sd).count m+
    (physicalMessages (SizeCount.sourceTable lastTable) tr t3 pub b sd).count m)=_
  rw [←List.count_append,←List.count_append,←List.count_append,counted_four_messages]
  have hsize : b≠B_SIZE := by simp only [B_SIZE]; omega
  simp only [hsize,ite_false]
  rw [first_reserved_messages tr t0 pub b hb,last_reserved_messages tr t3 pub b hb,
    middle_reserved_messages tr t1 pub 64 65 b hb,
    middle_reserved_messages tr t2 pub 65 66 b hb]
  cases sd <;> simp [eq_comm,List.append_assoc]

private theorem singleton_counts {a b : List Fp}
    (h : ∀ m,([a] : List (List Fp)).count m=([b] : List (List Fp)).count m) : a=b := by
  have hc := h a
  by_cases he : a=b
  · exact he
  · simp [Ne.symm he] at hc

/-- Bus64 authenticates the first-to-middle boundary for arbitrary accepted cells. -/
theorem first_boundary_equal {tr : Trace Fp} {t0 t1 t2 t3 : Nat} {pub : List Fp}
    (h : ∀ m,boundaryCount tr t0 t1 t2 t3 pub 64 true m=
      boundaryCount tr t0 t1 t2 t3 pub 64 false m) :
    carryRow tr t0 (tr.height t0-1)=carryRow tr t1 0 := by
  apply singleton_counts
  intro m
  simpa [boundary_count_exact tr t0 t1 t2 t3 pub 64 (by decide)] using h m

/-- Bus65 authenticates the middle-to-middle boundary without assuming placement. -/
theorem middle_boundary_equal {tr : Trace Fp} {t0 t1 t2 t3 : Nat} {pub : List Fp}
    (h : ∀ m,boundaryCount tr t0 t1 t2 t3 pub 65 true m=
      boundaryCount tr t0 t1 t2 t3 pub 65 false m) :
    carryRow tr t1 (tr.height t1-1)=carryRow tr t2 0 := by
  apply singleton_counts
  intro m
  simpa [boundary_count_exact tr t0 t1 t2 t3 pub 65 (by decide)] using h m

/-- Bus66 authenticates the middle-to-last boundary without assuming placement. -/
theorem last_boundary_equal {tr : Trace Fp} {t0 t1 t2 t3 : Nat} {pub : List Fp}
    (h : ∀ m,boundaryCount tr t0 t1 t2 t3 pub 66 true m=
      boundaryCount tr t0 t1 t2 t3 pub 66 false m) :
    carryRow tr t2 (tr.height t2-1)=carryRow tr t3 0 := by
  apply singleton_counts
  intro m
  simpa [boundary_count_exact tr t0 t1 t2 t3 pub 66 (by decide)] using h m

/-- All three full-row joins follow from isolated global bus balance. -/
theorem boundaries_equal {tr : Trace Fp} {t0 t1 t2 t3 : Nat} {pub : List Fp}
    (h : ∀ b∈([64,65,66] : List Nat),∀ m,
      boundaryCount tr t0 t1 t2 t3 pub b true m=
      boundaryCount tr t0 t1 t2 t3 pub b false m) :
    carryRow tr t0 (tr.height t0-1)=carryRow tr t1 0 ∧
    carryRow tr t1 (tr.height t1-1)=carryRow tr t2 0 ∧
    carryRow tr t2 (tr.height t2-1)=carryRow tr t3 0 := by
  exact ⟨first_boundary_equal (h 64 (by simp)),
    middle_boundary_equal (h 65 (by simp)),last_boundary_equal (h 66 (by simp))⟩

/-- Each authenticated tuple covers all57 source columns, including inactive
endpoint cells. No local row decomposition is needed for the bus extraction. -/
theorem boundaries_cells {tr : Trace Fp} {t0 t1 t2 t3 : Nat} {pub : List Fp}
    (h : ∀ b∈([64,65,66] : List Nat),∀ m,
      boundaryCount tr t0 t1 t2 t3 pub b true m=
      boundaryCount tr t0 t1 t2 t3 pub b false m) :
    (∀ x,x<57 → tr.cell t0 (tr.height t0-1) x=tr.cell t1 0 x) ∧
    (∀ x,x<57 → tr.cell t1 (tr.height t1-1) x=tr.cell t2 0 x) ∧
    (∀ x,x<57 → tr.cell t2 (tr.height t2-1) x=tr.cell t3 0 x) := by
  obtain ⟨h01,h12,h23⟩ := boundaries_equal h
  exact ⟨carry_cells tr t0 t1 h01,carry_cells tr t1 t2 h12,carry_cells tr t2 t3 h23⟩

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
