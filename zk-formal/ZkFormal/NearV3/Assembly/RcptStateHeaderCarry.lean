import ZkFormal.NearV3.Assembly.RcptStateHeaderFacts

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def headerCarryConstraints : List Expr :=
  [r,o2].map (fun col=>mul3 (c sCL) (Dsl.not (c fe)) (sub (n col) (c col)))

theorem headerCarryConstraints_in_states : ∀e∈headerCarryConstraints,e∈cStates := by
  intro e he
  simp only [cStates,List.mem_append]
  simp_all [headerCarryConstraints]

theorem planned_header_next_same (lists : List (List Input)) (pos : Nat) (p : ListPlan)
    (row : Coord) (b : PlannedRow)
    (ha : (plannedRows lists)[pos]?=some (.header p row))
    (hb : (plannedRows lists)[pos+1]?=some b)
    (hi : row.index+1<row.length) : b=.header p (advance row) := by
  rcases planned_index_neighbor_shape lists pos (.header p row) b ha hb with
    ⟨seg,_,a,_,hl,_,hea,heb⟩|⟨seg,a,_,hl,hend,hea⟩
  · cases seg with
    | header lp =>
      change PlannedRow.header p row=PlannedRow.header lp a at hea
      cases hea
      exact heb
    | receipt rp s => cases hea
  · cases seg with
    | header lp =>
      change PlannedRow.header p row=PlannedRow.header lp a at hea
      cases hea
      omega
    | receipt rp s => cases hea

theorem booleanReceiptTrace_headerCarry (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈headerCarryConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro e he
  obtain ⟨col,hcol,rfl⟩ := List.mem_map.mp he
  simp only [eval_mul3,eval_sub,eval_c,eval_not,eval_n]
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    rw [booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback sCL (by decide),ha]
    grind only
  | some a =>
    cases a with
    | receipt p row =>
      rw [booleanReceiptTrace_receipt_not_header own ctx lists log pos constants pub digests fallback headerFallback p row ha]
      grind only
    | header p row =>
      by_cases hend : row.index+1=row.length
      · rw [booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback fe (by decide)]
        simp only [ha,eraseRow,controlCell,fe,idx,act,fs,↓reduceIte,hend]
        grind only
      · have hi := planned_row_coord_bound lists (.header p row) (List.mem_of_getElem? ha)
        change row.index<row.length at hi
        have hin : row.index+1<row.length := by omega
        cases hb : (plannedRows lists)[pos+1]? with
        | none =>
          obtain ⟨seg,_,a,_,hl,he,hea⟩ := planned_before_padding lists pos (.header p row) ha hb
          have hh : (eraseRow (.header p row)).index+1=(eraseRow (.header p row)).length := by
            rw [hea,seg.erase_wrap];omega
          exact False.elim (hend hh)
        | some b =>
          have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hb).1 hcap
          have ht : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).height 0=2^log := rfl
          have heq := planned_header_next_same lists pos p row b ha hb hin
          subst b
          obtain ⟨_,_,_,hr,ho⟩ := booleanReceiptTrace_header_values own ctx lists log pos constants pub digests fallback headerFallback p row ha
          obtain ⟨_,_,_,hrn,hon⟩ := booleanReceiptTrace_header_values own ctx lists log (pos+1) constants pub digests fallback headerFallback p (advance row) hb
          rw [ht,Nat.mod_eq_of_lt hpos]
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hcol
          rcases hcol with rfl|rfl
          · rw [hr,hrn];grind only
          · rw [ho,hon];grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
