import ZkFormal.NearV3.Assembly.RcptGasFlagCurrent

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def gasFlagTransition : Expr := mul3 (c sGP) (Dsl.not (c fe)) (sub (n sumD) (.add (c sumD) DEn))

theorem gasFlag_transition_mem : gasFlagTransition∈cGas := by simp [gasFlagTransition,cGas,gp]

theorem gasFlag_transition_off (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sGP=0 ∨ tr.cell 0 pos fe=1) : gasFlagTransition.eval tr 0 pos pub=0 := by
  simp only [gasFlagTransition,eval_mul3,eval_c,eval_not]
  rcases hz with hz|hz <;> rw [hz] <;> grind only

theorem DEn_next (tr : Trace Fp) (tt pos : Nat) (pub : List Fp) :
    DEn.eval tr tt pos pub=DE.eval tr tt ((pos+1)%tr.height tt) pub := rfl

theorem booleanReceiptTrace_gasFlagTransition (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log) :
    gasFlagTransition.eval (booleanReceiptTrace own ctx lists log constants pub digests
      (gasFlagAux ctx (gasBorrowAux ctx fallback)) headerFallback) 0 pos pub=0 := by
  let tr := booleanReceiptTrace own ctx lists log constants pub digests
    (gasFlagAux ctx (gasBorrowAux ctx fallback)) headerFallback
  change gasFlagTransition.eval tr 0 pos pub=0
  have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests
    (gasFlagAux ctx (gasBorrowAux ctx fallback)) headerFallback
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply gasFlag_transition_off
    exact Or.inl (booleanReceiptTrace_padding own ctx lists log pos constants pub digests
      (gasFlagAux ctx (gasBorrowAux ctx fallback)) headerFallback ha sGP)
  | some a =>
    have hstate := hc sGP (by decide)
    rw [ha] at hstate
    dsimp only at hstate
    by_cases hs : (eraseRow a).state=sGP
    · cases a with
      | header p row =>
        have hh := planned_header_state lists p row (List.mem_of_getElem? ha)
        change row.state=sGP at hs
        rw [hh] at hs
        contradiction
      | receipt p row =>
        change row.state=sGP at hs
        by_cases he : row.index+1=row.length
        · apply gasFlag_transition_off
          apply Or.inr
          have hf := hc fe (by decide)
          rw [ha] at hf
          simpa only [eraseRow,controlCell,idx,act,fs,fe,Nat.reduceEqDiff,ite_true,ite_false,he] using hf
        · have hi := planned_row_coord_bound lists (.receipt p row) (List.mem_of_getElem? ha)
          change row.index<row.length at hi
          have hl := planned_receipt_field_length lists p row (List.mem_of_getElem? ha)
          rw [hs] at hl
          change row.length=16 at hl
          have hn := planned_receipt_next lists pos p row ha (by omega)
          have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hn).1 hcap
          have hcurr := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
            (gasFlagAux ctx (gasBorrowAux ctx fallback)) headerFallback _ ha
          have hnext := booleanReceiptTrace_planned_cell own ctx lists log (pos+1) constants pub digests
            (gasFlagAux ctx (gasBorrowAux ctx fallback)) headerFallback _ hn
          have h0 : tr.cell 0 pos sumD=Fp.ofNat (gasDifferenceSum ctx p.input.receipt (row.index+1)) := by
            apply (hcurr sumD (by decide)).trans
            cases row with
            | mk state i len =>
              dsimp only at hs
              subst state
              exact gasFlag_sum_cell ctx constants pub digests (receiptPlanToken ctx lists) (gasBorrowAux ctx fallback) p i len
          have h1 : tr.cell 0 (pos+1) sumD=Fp.ofNat (gasDifferenceSum ctx p.input.receipt (row.index+2)) := by
            apply (hnext sumD (by decide)).trans
            cases row with
            | mk state i len =>
              dsimp only at hs
              subst state
              exact gasFlag_sum_cell ctx constants pub digests (receiptPlanToken ctx lists) (gasBorrowAux ctx fallback) p (i+1) len
          have hd : DEn.eval tr 0 pos pub=Fp.ofNat (gasDifference ctx p.input.receipt (row.index+1)) := by
            rw [DEn_next,show tr.height 0=2^log from rfl,Nat.mod_eq_of_lt hpos]
            rw [show DE=bitsX 0 8 from rfl,RoutingBoundedLayout.eval_frame_bits tr 0 (pos+1) pub 0
              (gasDifference ctx p.input.receipt (row.index+1)) 8 ?_]
            · rw [Nat.mod_eq_of_lt (gasDifference_lt ctx p.input.receipt (row.index+1))]
            · intro j hj
              simp only [Nat.zero_add]
              have hjc : emissionColumn (xb j)=false := by
                have hj8 : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
                rcases hj8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
              rw [hnext (xb j) hjc]
              cases row with
              | mk state i len =>
                dsimp only at hs
                subst state
                rw [←gasBorrow_flag_commute]
                exact gasDifference_bit_cell ctx constants pub digests (receiptPlanToken ctx lists)
                  (gasFlagAux ctx fallback) p (i+1) len j hj
          simp only [gasFlagTransition,eval_mul3,eval_sub,eval_n,eval_c,eval_add]
          change _ * _ * (tr.cell 0 ((pos+1)%2^log) sumD-(tr.cell 0 pos sumD+DEn.eval tr 0 pos pub))=0
          rw [Nat.mod_eq_of_lt hpos,h1,h0,hd]
          have hsum : Fp.ofNat (gasDifferenceSum ctx p.input.receipt (row.index+2))=
              Fp.ofNat (gasDifferenceSum ctx p.input.receipt (row.index+1))+Fp.ofNat (gasDifference ctx p.input.receipt (row.index+1)) :=
            ZkFormal.Near.Render.RcptP.ofNat_add_e _ _
          rw [hsum]
          grind only

    · apply gasFlag_transition_off
      exact Or.inl (hstate.trans (by rw [control_state _ (by decide),if_neg (Ne.symm hs)]))

end ZkFormal.NearV3.Assembly.RcptSkeleton
