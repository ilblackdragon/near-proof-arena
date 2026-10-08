import ZkFormal.NearV3.Assembly.RcptPhysicalHeaders

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Every ordinary register subgroup on a receipt segment interior, sharing
one stream/token assignment. -/
theorem receipt_ordinaryRegs_interior (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord)
    (hlen : row.length=fieldLen plan.input row.state) (hi : row.index+1<row.length) :
    ∀e∈ordinaryRegs,e.eval
      (receiptPair constants (tokenReceiptAux pub digests tokens fallback) plan row (advance row)) 0 0 pub=0 := by
  intro e he
  simp only [ordinaryRegs,List.mem_append,or_assoc] at he
  rcases he with he|he|he|he|he
  · exact stream_load_constraints constants digests (tokenAux tokens fallback) plan row (advance row) pub e he
  · have he' : e=byteHeadConstraint := by simpa only [List.mem_singleton] using he
    subst e
    exact stream_byte_head constants digests (tokenAux tokens fallback) plan row (advance row) pub
  · exact stream_shift_constraints constants digests (tokenAux tokens fallback) plan row pub e he
  · by_cases hs : row.state=sGP
    · cases row with
      | mk s i len =>
        dsimp only at hs hlen hi
        subst s
        have hlen' : len=16 := by simpa [fieldLen,sGP,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK] using hlen
        subst len
        have hp : i+1<16 := hi
        have hh := receipt_gas_token_constraints constants pub digests tokens fallback plan i (by omega) e he
        simpa [nextGas,hp,advance,fieldLen,sGP,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK] using hh
    · have hz : receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan row sGP=0 := by
        rw [receipt_control_cell _ _ _ _ (by decide),control_state _ (by decide)]
        simp [Ne.symm hs]
      simp only [gasTokenConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with he|rfl
      · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
        simp only [eval_mul,eval_sub,eval_c,eval_n]
        change receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan row sGP*_=0
        rw [hz]
        grind only
      · simp only [eval_mul,eval_sub,eval_c,eval_n]
        change receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan row sGP*_=0
        rw [hz]
        grind only
  · by_cases hs : row.state=sGP
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
      simp only [eval_mul,eval_sub,eval_c,eval_n]
      cases row with
      | mk s i len =>
        dsimp only at hs
        subst s
        have hz : receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan ⟨sGP,i,len⟩ lastR=0 := by
          change bitCell (receiptEnd plan ⟨sGP,i,len⟩ && plan.lastInList && plan.lastList)=0
          simp [receiptEnd,sGP,sXRZ,sXLH,bitCell]
        change ((1:Fp)-1-receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan ⟨sGP,i,len⟩ lastR)*_=0
        rw [hz]
        grind only
    · exact receipt_token_carry_internal constants pub digests tokens fallback plan row hs e he

/-- Full cRegs on actual receipt-interior trace rows, with native prefix-ledger
tokens and the same header initialization assignment as the header theorem. -/
theorem planned_receipt_cRegs (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord)
    (hlen : row.length=fieldLen plan.input row.state) (hi : row.index+1<row.length)
    (ha : (plannedRows lists)[pos]?=some (.receipt plan row))
    (hb : (plannedRows lists)[pos+1]?=some (.receipt plan (advance row)))
    (hh : pos+1<2^log) :
    ∀e∈cRegs,e.eval
      (plannedTrace lists log constants
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
        (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback)) 0 pos pub=0 := by
  intro e he
  rcases (cRegs_membership e).mp he with he|he
  · apply planned_ordinaryRegs_transport lists log pos constants _ _ _ _ ha hb hh
      (receiptPair constants (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback) plan row (advance row)) 0 0 pub
    · intro c; rfl
    · intro c; rfl
    · exact receipt_ordinaryRegs_interior constants pub digests (receiptPlanToken ctx lists) fallback plan row hlen hi
    · exact he
  · exact planned_stream_initial_tokens own ctx _ lists log pos constants _ headerFallback pub e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
