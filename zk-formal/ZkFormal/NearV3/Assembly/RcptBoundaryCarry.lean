import ZkFormal.NearV3.Assembly.RcptSegmentTokenCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Actual active-to-active boundary carry, including all source-list header
transitions. Every equality is derived from the row plan and native prefix sum. -/
theorem planned_boundary_token_carry (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (a b : PlannedRow) (ha : (plannedRows lists)[pos]?=some a) (hb : (plannedRows lists)[pos+1]?=some b)
    (hend : (eraseRow a).index+1=(eraseRow a).length) (hs : (eraseRow a).state≠sGP)
    (hh : pos+1<2^log) :
    ∀e∈carryTokenConstraints,e.eval
      (plannedTrace lists log constants
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
        (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback)) 0 pos pub=0 := by
  have hn := neighbors_of_get _ a b pos ha hb
  rcases planned_neighbors_indexed lists hw a b hn with ⟨p,_,hn⟩|⟨p,q,hpq,hp,hq,_⟩
  · obtain ⟨row,_,hlen,hi,hrow,_⟩ := p.neighbors a b hn
    rw [hrow,p.erase_wrap] at hend
    omega
  · have hps : p.state≠sGP := by
      obtain ⟨row,hstate,_,_,hrow⟩ := p.last a hp
      simpa only [hrow,p.erase_wrap,hstate] using hs
    intro e he
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hj' := List.mem_range.mp hj
    have hbytes := segment_boundary_token_cells own ctx lists constants pub digests fallback headerFallback
      p q hpq a b hp hq hps j hj'
    simp only [eval_mul,eval_sub,eval_c,eval_n]
    have hc := plannedTrace_cell lists log pos constants
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
      (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback) a ha (tok j)
    have hn := plannedTrace_cell lists log (pos+1) constants
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
      (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback) b hb (tok j)
    change _* ((plannedTrace lists log constants _ _).cell 0 ((pos+1)%2^log) (tok j)-
      (plannedTrace lists log constants _ _).cell 0 pos (tok j))=0
    rw [Nat.mod_eq_of_lt hh,hn,hc]
    change _*(nativePlannedCell own ctx lists constants pub digests fallback headerFallback b (tok j)-
      nativePlannedCell own ctx lists constants pub digests fallback headerFallback a (tok j))=0
    rw [hbytes]
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
