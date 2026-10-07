import ZkFormal.NearV3.Public.Index

/-! Exact source, routing, and refund-body natural message families. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra NearSpecV3

def sourceRecords (p : Prep) : List (List Nat) :=
  (List.range p.lists.length).map fun j =>
    [j, if sourceDup p.lists j then 1 else 0] ++
      (p.lists.getD j ⟨[],0,[]⟩).root.map UInt8.toNat

def boundaryRecords (p : Prep) : List (List Nat) :=
  (List.range (BND_STRIDE*p.bnds.length)).map fun x => [x] ++ (boundaryRow p.bnds x).map UInt8.toNat

def bodyRecords (p : Prep) : List (List Nat) :=
  (List.range (p.body.length-8)).map fun j => [2,8+j,(p.body.getD (8+j) 0).toNat]

theorem prepared_source_records (p : Prep) : preparedOn p B_SRC true = sourceRecords p := by
  rw [preparedOn_source]
  unfold preparedRecords
  rw [descriptor_index]
  change (List.range (sourcePayload p.lists).length).map _ = _
  rw [sourcePayload_length]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  change recordNats (descriptor sourcePlan 202 0) j ((sourcePayload p.lists).getD j []) = _
  rw [sourcePayload_getD p.lists hj]
  simp only [recordNats,descriptor,sourcePlan,List.nil_append,Nat.zero_add]
  unfold sourceRow
  cases sourceDup p.lists j <;> rfl

theorem prepared_boundary_records (p : Prep) :
    preparedOn p B_BNDP true = boundaryRecords p := by
  rw [preparedOn_boundary]
  unfold preparedRecords
  rw [descriptor_index]
  change (List.range (boundaryPayload p.bnds).length).map _ = _
  rw [boundaryPayload_length]
  apply List.map_congr_left
  intro x hx
  change recordNats (descriptor boundaryPlan 202 1) x ((boundaryPayload p.bnds).getD x []) = _
  rw [boundaryPayload_getD p.bnds (List.mem_range.mp hx)]
  simp only [recordNats,descriptor,boundaryPlan,List.nil_append,Nat.zero_add]

theorem body_nat_record (body : ByteString) {j : Nat} (hj : j < body.length-8) :
    recordNats bodyPlan j ((bodyPayload body).getD j []) = [2,8+j,(body.getD (8+j) 0).toNat] := by
  have hdrop : j < (body.drop 8).length := by simpa using hj
  have hmap : j < (bodyPayload body).length := by simpa [bodyPayload] using hdrop
  rw [← List.getElem_eq_getD (h := hmap) []]
  simp only [bodyPayload,List.getElem_map,List.getElem_drop]
  rw [← List.getElem_eq_getD (h := (show 8+j < body.length by omega)) 0]
  rfl

theorem prepared_body_records (p : Prep) : preparedOn p 0 false = bodyRecords p := by
  rw [preparedOn_body]
  unfold preparedRecords
  rw [descriptor_index]
  change (List.range (bodyPayload p.body).length).map _ = _
  rw [bodyPayload_length]
  apply List.map_congr_left
  intro j hj
  exact body_nat_record p.body (List.mem_range.mp hj)

theorem prepared_receipt_index (AP : AirP) (p : Prep) (witnessOverhead : Nat)
    (hseg : AP.pubSegs = preparedSegments) (hr : RootsSized p)
    (hs : ∀ s ∈ p.lists, s.root.length = 32)
    (hlen : (preparedBytes p witnessOverhead).length < 256^4) :
    let I := prepared_pubIdx AP p witnessOverhead hseg hr hs hlen
    I.recs B_SRC true = sourceRecords p ∧ I.recs B_BNDP true = boundaryRecords p ∧
    I.recs 0 false = bodyRecords p := by
  dsimp only
  simp only [prepared_pubIdx_recs]
  exact ⟨prepared_source_records p,prepared_boundary_records p,prepared_body_records p⟩

end ZkFormal.NearV3.Public
