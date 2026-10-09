import ZkFormal.NearV3.Assembly.RcptStateSizes

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def firstStateConstraints : List Expr :=
  [.mul .isFirst (Dsl.not (c sCL)),.mul .isFirst (Dsl.not (c fs)),.mul .isFirst (c idx),
   .mul .isFirst (c j),.mul .isFirst (c r),.mul .isFirst (sub (c o2) (k 8))]

theorem firstStateConstraints_in_states : ∀e∈firstStateConstraints,e∈cStates := by
  intro e he
  simp only [firstStateConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cStates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem booleanReceiptTrace_first_cells (own : Nat) (ctx : ApplyCtx) (xs : List Input)
    (lists : List (List Input)) (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    let tr := booleanReceiptTrace own ctx (xs::lists) log constants pub digests fallback headerFallback
    tr.cell 0 0 sCL=1 ∧ tr.cell 0 0 fs=1 ∧ tr.cell 0 0 idx=0 ∧
    tr.cell 0 0 j=0 ∧ tr.cell 0 0 r=0 ∧ tr.cell 0 0 o2=8 := by
  dsimp only
  unfold booleanReceiptTrace emittedReceiptTrace
  have ha := planned_first_header xs lists
  have hc := plannedTrace_cell (xs::lists) log 0 (booleanConstants constants)
    (tokenReceiptAux pub digests (receiptPlanToken ctx (xs::lists)) (booleanReceiptAux fallback))
    (headerStreamAux own (headerBurn ctx ((xs::lists).flatten.map Input.receipt))
      (emissionHeaderFallback (booleanHeaderAux headerFallback))) _ ha
  constructor
  · rw [emissionPatch_other _ _ _ _ _ sCL (by decide)];exact hc sCL
  constructor
  · rw [emissionPatch_other _ _ _ _ _ fs (by decide)];exact hc fs
  constructor
  · rw [emissionPatch_other _ _ _ _ _ idx (by decide)];exact hc idx
  constructor
  · rw [emissionPatch_other _ _ _ _ _ j (by decide)];exact hc j
  constructor
  · rw [emissionPatch_other _ _ _ _ _ r (by decide)];exact hc r
  · rw [emissionPatch_other _ _ _ _ _ o2 (by decide)];exact hc o2

theorem booleanReceiptTrace_firstState (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hne : lists≠[]) (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈firstStateConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  cases lists with
  | nil => exact False.elim (hne rfl)
  | cons xs lists =>
    intro e he
    have hh := booleanReceiptTrace_first_cells own ctx xs lists log constants pub digests fallback headerFallback
    simp only [firstStateConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [eval_mul,eval_isFirst,eval_c,eval_not,eval_sub,eval_k]
    all_goals by_cases hp : pos=0
    all_goals first | (subst pos; simp only [ite_true,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2];grind only) | (rw [if_neg hp];grind only)

theorem booleanReceiptTrace_lastInactive (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length<2^log) :
    (Expr.mul .isLast (c act)).eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  have ht : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).height 0=2^log := rfl
  simp only [eval_mul,eval_isLast,eval_c,ht]
  split
  · rename_i hp
    have hn : (plannedRows lists)[pos]?=none := List.getElem?_eq_none (by omega)
    rw [booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback act (by decide),hn]
    grind only
  · grind only

theorem booleanReceiptTrace_paddingMonotone (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hpos : pos<2^log) :
    (mul3 .isTransition (Dsl.not (c act)) (n act)).eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  have ht : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).height 0=2^log := rfl
  simp only [eval_mul3,eval_isTransition,eval_not,eval_c,eval_n,ht]
  split
  · grind only
  · rename_i hp
    have hlt : pos+1<2^log := by omega
    rw [Nat.mod_eq_of_lt hlt]
    cases ha : (plannedRows lists)[pos]? with
    | none =>
      have hn : (plannedRows lists)[pos+1]?=none := List.getElem?_eq_none (by have hh := List.getElem?_eq_none_iff.mp ha;omega)
      rw [booleanReceiptTrace_control own ctx lists log (pos+1) constants pub digests fallback headerFallback act (by decide),hn]
      grind only
    | some a =>
      rw [booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback act (by decide)]
      simp only [ha,controlCell,act,idx,↓reduceIte]
      grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
