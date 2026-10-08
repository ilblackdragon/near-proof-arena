import ZkFormal.NearV3.Assembly.RcptPhysicalInterior

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- All register constraints vanish on zero padding, even when the next row
wraps to an active first row. No premise is needed on the next cells. -/
theorem zero_row_cRegs (tr : Trace Fp) (t pos : Nat) (pub : List Fp)
    (hz : ∀col,tr.cell t pos col=0) : ∀e∈cRegs,e.eval tr t pos pub=0 := by
  intro e he
  rcases (cRegs_membership e).mp he with he|he
  · simp only [ordinaryRegs,List.mem_append,or_assoc] at he
    rcases he with he|he|he|he|he
    · obtain ⟨⟨s,es⟩,_,he⟩ := List.mem_flatMap.mp he
      obtain ⟨⟨ee,j⟩,_,rfl⟩ := List.mem_map.mp he
      simp only [eval_mul3,eval_c,hz,eval_sub]
      grind only
    · have he' : e=byteHeadConstraint := by simpa only [List.mem_singleton] using he
      subst e
      simp only [byteHeadConstraint,eval_mul,eval_sub,eval_c,hz]
      grind only
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
      simp only [eval_mul3,eval_not,eval_sub,eval_c,hz,eval_n]
      grind only
    · simp only [gasTokenConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with he|rfl
      · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
        simp only [eval_mul,eval_sub,eval_c,hz,eval_n]
        grind only
      · simp only [eval_mul,eval_sub,eval_c,hz,eval_n]
        grind only
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
      simp only [eval_mul,eval_sub,eval_c,hz,eval_n]
      grind only
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
    simp only [eval_mul,eval_c,hz]
    grind only

theorem planned_padding_cRegs (lists : List (List Input)) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (ra : ReceiptPlan→Coord→Nat→Fp)
    (ha : ListPlan→Coord→Nat→Fp) (pub : List Fp) (hp : (plannedRows lists).length≤pos) :
    ∀e∈cRegs,e.eval (plannedTrace lists log constants ra ha) 0 pos pub=0 :=
  zero_row_cRegs _ 0 pos pub (plannedTrace_padding lists log pos constants ra ha hp)

end ZkFormal.NearV3.Assembly.RcptSkeleton
