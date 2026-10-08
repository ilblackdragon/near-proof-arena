import ZkFormal.NearV3.Assembly.RcptRegInterior

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem SegmentPlan.erase_wrap (p : SegmentPlan) (row : Coord) : eraseRow (p.wrap row)=row := by
  cases p <;> rfl

/-- Unified physical cRegs for every nonterminal segment coordinate. The actual
row-neighbor classification chooses header versus receipt and supplies the
matching next-row annotation; no adjacency witness is an input. -/
theorem planned_interior_cRegs (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (a b : PlannedRow)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat))
    (ha : (plannedRows lists)[pos]?=some a) (hb : (plannedRows lists)[pos+1]?=some b)
    (hi : (eraseRow a).index+1<(eraseRow a).length) (hh : pos+1<2^log) :
    ∀e∈cRegs,e.eval
      (plannedTrace lists log constants
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
        (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback)) 0 pos pub=0 := by
  rcases planned_index_neighbor_shape lists pos a b ha hb with
    ⟨p,_,row,hs,hl,hint,hea,heb⟩|⟨p,row,_,hl,hend,hea⟩
  · subst a b
    have hin : row.index+1<row.length := by simpa only [p.erase_wrap] using hi
    cases p with
    | header plan =>
      change row.state=sCL at hs
      change row.length=12 at hl
      cases row with
      | mk state index len =>
        dsimp only at hs hl
        subst state len
        exact planned_header_cRegs own ctx _ lists log pos index constants _ headerFallback plan pub hown ha hb hh
    | receipt plan state =>
      change row.state=state at hs
      change row.length=fieldLen plan.input state at hl
      have hlen : row.length=fieldLen plan.input row.state := by rw [hs];exact hl
      exact planned_receipt_cRegs own ctx lists log pos constants pub digests fallback headerFallback plan row hlen
        hin ha hb hh
  · rw [hea,p.erase_wrap] at hi
    omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
