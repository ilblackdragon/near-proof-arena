import ZkFormal.NearV3.Assembly.RcptSkeletonLoadCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem loadConstraints_count : loadConstraints.length=120 := by decide

/-- Every original load polynomial vanishes in the shared receipt row constructor
with its executable register stream. This includes inactive load states and
noninitial rows, not just the single selected state/byte. -/
theorem receipt_load_constraints (constants : ReceiptPlan→Nat→Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row next : Coord)
    (pub : List Fp) :
    ∀e∈loadConstraints,e.eval (receiptPair constants (registerAux pub fallback) plan row next) 0 0 pub=0 := by
  intro e he
  obtain ⟨⟨state,es⟩,hm,he⟩ := List.mem_flatMap.mp he
  obtain ⟨⟨expr,j⟩,hmem,rfl⟩ := List.mem_map.mp he
  have hstate := loads_states (state,es) hm
  have hlim := states_limits hstate
  have hcstate : controlColumn state=true := by simp [controlColumn];omega
  have hcol : (receiptPair constants (registerAux pub fallback) plan row next).cell 0 0 state=
      if state=row.state then 1 else 0 := by
    change receiptCell constants (registerAux pub fallback) plan row state=_
    rw [receipt_control_cell constants _ plan row hcstate,control_state row hstate]
  have hfs : (receiptPair constants (registerAux pub fallback) plan row next).cell 0 0 fs=
      if row.index=0 then 1 else 0 := by
    change receiptCell constants (registerAux pub fallback) plan row fs=_
    rw [receipt_control_cell constants _ plan row (by decide)]
    rfl
  simp only [eval_mul3,eval_c,eval_sub,hcol,hfs]
  by_cases hi : row.index=0
  · rw [if_pos hi]
    by_cases hs : state=row.state
    · rw [if_pos hs]
      have hj : j<32 := by
        have h0 := List.mem_range.mp (List.of_mem_zip hmem).2
        have hl : es.length≤32 := loads_length (state,es) hm
        omega
      have hreg : (receiptPair constants (registerAux pub fallback) plan row next).cell 0 0 (reg j)=
          expr.eval (shapeTrace plan.input) 0 0 pub := by
        change receiptCell constants (registerAux pub fallback) plan row (reg j)=_
        rw [receipt_register_cell constants fallback plan row pub j hj,hi,←hs]
        exact register_load_entry plan.input pub hm hmem
      have heval := receipt_load_expr constants (registerAux pub fallback) plan row next pub hm
        (List.of_mem_zip hmem).1
      rw [hreg,heval]
      grind only
    · rw [if_neg hs]
      grind only
  · rw [if_neg hi]
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
