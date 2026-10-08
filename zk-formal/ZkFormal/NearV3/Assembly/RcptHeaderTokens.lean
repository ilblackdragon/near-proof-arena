import ZkFormal.NearV3.Assembly.RcptTokenCarry
import ZkFormal.NearV3.Assembly.RcptMainTokenLedger

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Header rows hold the running burn total at entry to their receipt list. -/
def tokenHeaderAux (before : ListPlan→Nat) (fallback : ListPlan→Coord→Nat→Fp)
    (plan : ListPlan) (row : Coord) (col : Nat) : Fp :=
  if tok 0≤col ∧ col<tok 16 then
    Fp.ofNat (((u128 (before plan)).getD (col-tok 0) 0).toNat)
  else fallback plan row col

theorem header_token_cell (before : ListPlan→Nat) (fallback : ListPlan→Coord→Nat→Fp)
    (plan : ListPlan) (row : Coord) (j : Nat) (hj : j<16) :
    headerCell (tokenHeaderAux before fallback) plan row (tok j)=
      Fp.ofNat (((u128 (before plan)).getD j 0).toNat) := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 := by omega
  rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst j <;> rfl

def initialTokenConstraints : List Expr :=
  (List.range 16).map fun j=>.mul .isFirst (c (tok j))

theorem initialToken_in_regs : ∀e∈initialTokenConstraints,e∈cRegs := by
  intro e he
  simp only [cRegs,List.mem_append]
  simp only [initialTokenConstraints] at he
  grind only

theorem u128_zero_byte (j : Nat) : (u128 0).getD j 0=0 := by
  change (List.replicate 16 (0:UInt8)).getD j 0=0
  rw [List.getD_eq_getElem?_getD,List.getElem?_replicate]
  split <;> rfl

/-- The zero-initialized header satisfies all 16 actual initial-token equations. -/
theorem header_initial_tokens (before : ListPlan→Nat) (fallback : ListPlan→Coord→Nat→Fp)
    (plan : ListPlan) (row : Coord) (hb : before plan=0) (log : Nat) (pub : List Fp) :
    ∀e∈initialTokenConstraints,e.eval
      ⟨fun _=>log,fun _ _ col=>headerCell (tokenHeaderAux before fallback) plan row col⟩ 0 0 pub=0 := by
  intro e he
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
  have hj' := List.mem_range.mp hj
  simp only [eval_mul,eval_c]
  change _*headerCell (tokenHeaderAux before fallback) plan row (tok j)=0
  rw [header_token_cell _ _ _ _ _ hj',hb,u128_zero_byte]
  change _*(0:Fp)=0
  grind only

/-- All header-to-header token carries hold for the same entry total. -/
theorem header_token_carry (before : ListPlan→Nat) (fallback : ListPlan→Coord→Nat→Fp)
    (plan : ListPlan) (row next : Coord) (pub : List Fp) :
    ∀e∈carryTokenConstraints,e.eval
      ⟨fun _=>1,fun _ pos col=>headerCell (tokenHeaderAux before fallback) plan
        (if pos=0 then row else next) col⟩ 0 0 pub=0 := by
  intro e he
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
  have hj' := List.mem_range.mp hj
  simp only [eval_mul,eval_sub,eval_c,eval_n]
  change _*(headerCell (tokenHeaderAux before fallback) plan next (tok j)-
    headerCell (tokenHeaderAux before fallback) plan row (tok j))=0
  rw [header_token_cell _ _ _ _ _ hj',header_token_cell _ _ _ _ _ hj']
  grind only

/-- Header totals use the same global ordered receipt prefix as receipt windows. -/
def headerBurn (ctx : ApplyCtx) (receipts : List Receipt) (plan : ListPlan) : Nat :=
  ((receipts.take plan.receiptIndex).map (nativeBurn ctx)).sum

theorem first_header_burn (ctx : ApplyCtx) (receipts : List Receipt) (xs : List Input)
    (lastList : Bool) : headerBurn ctx receipts ⟨xs,0,0,8,lastList⟩=0 := rfl

theorem planned_first_header (xs : List Input) (lists : List (List Input)) :
    (plannedRows (xs::lists))[0]? =
      some (.header ⟨xs,0,0,8,lists.isEmpty⟩ ⟨sCL,0,12⟩) := by
  rfl

/-- Actual physical planned trace, not just an isolated header pair, has zero
initial tokens under the native prefix-sum assignment. -/
theorem planned_initial_token_cells (ctx : ApplyCtx) (receipts : List Receipt)
    (lists : List (List Input)) (log : Nat) (constants : ReceiptPlan→Nat→Fp)
    (ra : ReceiptPlan→Coord→Nat→Fp) (fallback : ListPlan→Coord→Nat→Fp)
    (j : Nat) (hj : j<16) :
    (plannedTrace lists log constants ra (tokenHeaderAux (headerBurn ctx receipts) fallback)).cell 0 0 (tok j)=0 := by
  cases lists with
  | nil => rfl
  | cons xs lists =>
    simp only [plannedTrace,planned_first_header,plannedCell]
    rw [header_token_cell _ _ _ _ _ hj,first_header_burn,u128_zero_byte]
    rfl

theorem planned_initial_tokens (ctx : ApplyCtx) (receipts : List Receipt)
    (lists : List (List Input)) (log : Nat) (constants : ReceiptPlan→Nat→Fp)
    (ra : ReceiptPlan→Coord→Nat→Fp) (fallback : ListPlan→Coord→Nat→Fp)
    (pub : List Fp) :
    ∀e∈initialTokenConstraints,e.eval
      (plannedTrace lists log constants ra (tokenHeaderAux (headerBurn ctx receipts) fallback)) 0 0 pub=0 := by
  intro e he
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
  have hj' := List.mem_range.mp hj
  simp only [eval_mul,eval_c]
  rw [planned_initial_token_cells _ _ _ _ _ _ _ _ hj']
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
