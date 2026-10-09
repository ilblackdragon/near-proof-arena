import ZkFormal.NearV3.Assembly.RcptRegTransport

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Final header-stream assignment preserves actual zero initialization. -/
theorem planned_stream_initial_cell (own : Nat) (ctx : ApplyCtx) (rs : List Receipt)
    (lists : List (List Input)) (log : Nat) (constants : ReceiptPlan→Nat→Fp)
    (ra : ReceiptPlan→Coord→Nat→Fp) (fallback : ListPlan→Coord→Nat→Fp)
    (j : Nat) (hj : j<16) :
    (plannedTrace lists log constants ra (headerStreamAux own (headerBurn ctx rs) fallback)).cell 0 0 (tok j)=0 := by
  cases lists with
  | nil => rfl
  | cons xs lists =>
    simp only [plannedTrace,planned_first_header,plannedCell]
    rw [header_stream_token _ _ _ _ _ _ hj,first_header_burn,u128_zero_byte]
    rfl

theorem planned_stream_initial_tokens (own : Nat) (ctx : ApplyCtx) (rs : List Receipt)
    (lists : List (List Input)) (log pos : Nat) (constants : ReceiptPlan→Nat→Fp)
    (ra : ReceiptPlan→Coord→Nat→Fp) (fallback : ListPlan→Coord→Nat→Fp) (pub : List Fp) :
    ∀e∈initialTokenConstraints,e.eval
      (plannedTrace lists log constants ra (headerStreamAux own (headerBurn ctx rs) fallback)) 0 pos pub=0 := by
  intro e he
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
  have hj' := List.mem_range.mp hj
  simp only [eval_mul,eval_c,eval_isFirst]
  by_cases hp : pos=0
  · subst pos
    rw [planned_stream_initial_cell _ _ _ _ _ _ _ _ _ hj']
    grind only
  · simp [hp]
    grind only

/-- Full cRegs at an actual physical header interior, including the global first
row. Current/next cell agreement is derived from the indexed constructor. -/
theorem planned_header_cRegs (own : Nat) (ctx : ApplyCtx) (rs : List Receipt)
    (lists : List (List Input)) (log pos i : Nat) (constants : ReceiptPlan→Nat→Fp)
    (ra : ReceiptPlan→Coord→Nat→Fp) (fallback : ListPlan→Coord→Nat→Fp)
    (plan : ListPlan) (pub : List Fp)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat))
    (ha : (plannedRows lists)[pos]?=some (.header plan ⟨sCL,i,12⟩))
    (hb : (plannedRows lists)[pos+1]?=some (.header plan ⟨sCL,i+1,12⟩))
    (hh : pos+1<2^log) :
    ∀e∈cRegs,e.eval
      (plannedTrace lists log constants ra (headerStreamAux own (headerBurn ctx rs) fallback)) 0 pos pub=0 := by
  intro e he
  rcases (cRegs_membership e).mp he with he|he
  · apply planned_ordinaryRegs_transport lists log pos constants ra _ _ _ ha hb hh
      (headerRegPair own (headerBurn ctx rs) fallback plan i) 0 1 pub
    · intro c; rfl
    · intro c; rfl
    · intro e he
      exact header_cRegs_public own _ fallback plan i pub hown e ((cRegs_membership e).mpr (Or.inl he))
    · exact he
  · exact planned_stream_initial_tokens own ctx rs lists log pos constants ra fallback pub e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
