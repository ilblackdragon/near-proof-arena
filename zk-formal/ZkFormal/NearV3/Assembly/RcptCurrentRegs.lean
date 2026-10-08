import ZkFormal.NearV3.Assembly.RcptBoundaryCarry

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def currentRegs : List Expr := loadConstraints++[byteHeadConstraint]
def currentExpr : Expr→Bool
  | .const _ | .pub _=>true
  | .col _ nx=> !nx
  | .add a b | .mul a b=>currentExpr a && currentExpr b
  | .neg a=>currentExpr a
  | _=>false

set_option maxRecDepth 4096 in
theorem currentRegs_footprint : currentRegs.all currentExpr=true := by decide

theorem currentExpr_eval (tr tr' : Trace Fp) (t r t' r' : Nat) (pub : List Fp)
    (hc : ∀c,tr.cell t r c=tr'.cell t' r' c) (e : Expr) (he : currentExpr e=true) :
    e.eval tr t r pub=e.eval tr' t' r' pub := by
  induction e with
  | const => rfl
  | pub => rfl
  | col c nx => cases nx with | false=>exact hc c | true=>cases he
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hh : currentExpr a=true ∧ currentExpr b=true := by simpa only [currentExpr,Bool.and_eq_true] using he
    simp only [eval_add,ia hh.1,ib hh.2]
  | mul a b ia ib =>
    have hh : currentExpr a=true ∧ currentExpr b=true := by simpa only [currentExpr,Bool.and_eq_true] using he
    simp only [eval_mul,ia hh.1,ib hh.2]
  | neg a ia => simp only [eval_neg,ia he]

theorem receipt_currentRegs (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord) :
    ∀e∈currentRegs,e.eval
      (receiptPair constants (tokenReceiptAux pub digests tokens fallback) plan row row) 0 0 pub=0 := by
  intro e he
  simp only [currentRegs,List.mem_append,List.mem_singleton] at he
  rcases he with he|rfl
  · exact stream_load_constraints constants digests (tokenAux tokens fallback) plan row row pub e he
  · exact stream_byte_head constants digests (tokenAux tokens fallback) plan row row pub

/-- Actual current-row groups are valid on every generated segment coordinate,
including endpoints; they impose no next-row agreement premise. -/
theorem planned_currentRegs (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : SegmentPlan) (row : Coord)
    (hs : row.state=p.state) (hl : row.length=p.length)
    (ha : (plannedRows lists)[pos]?=some (p.wrap row))
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀e∈currentRegs,e.eval
      (plannedTrace lists log constants
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
        (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback)) 0 pos pub=0 := by
  intro e he
  have hf := List.all_eq_true.mp currentRegs_footprint e he
  cases p with
  | receipt rp state =>
    rw [currentExpr_eval _ (receiptPair constants (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback) rp row row)
      0 pos 0 0 pub ?_ e hf]
    · exact receipt_currentRegs constants pub digests (receiptPlanToken ctx lists) fallback rp row e he
    · intro c;exact plannedTrace_cell lists log pos constants _ _ _ ha c
  | header lp =>
    change row.state=sCL at hs
    change row.length=12 at hl
    cases row with
    | mk state i len =>
      dsimp only at hs hl
      subst state len
      rw [currentExpr_eval _ (headerRegPair own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback lp i)
        0 pos 0 1 pub ?_ e hf]
      · apply header_cRegs_public own _ headerFallback lp i pub hown e
        apply (cRegs_membership e).mpr ∘ Or.inl
        simp only [currentRegs,List.mem_append,List.mem_singleton] at he
        simp only [ordinaryRegs,List.mem_append,List.mem_singleton]
        grind only
      · intro c;exact plannedTrace_cell lists log pos constants _ _ _ ha c

end ZkFormal.NearV3.Assembly.RcptSkeleton
