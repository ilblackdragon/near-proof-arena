import ZkFormal.NearV3.Assembly.RcptKeyAccountLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def keyZeroConstraint : Expr := mul3 (c sVL) (Dsl.not (c fe)) (sub (n kz) (c fs))

theorem keyZero_constraint_mem : keyZeroConstraint∈cKey := by simp [keyZeroConstraint,cKey]

theorem keyZero_constraint_off (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sVL=0 ∨ tr.cell 0 pos fe=1) : keyZeroConstraint.eval tr 0 pos pub=0 := by
  simp only [keyZeroConstraint,eval_mul3,eval_c,eval_not]
  rcases hz with hz|hz <;> rw [hz] <;> grind only

theorem booleanReceiptTrace_keyZero (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log) :
    keyZeroConstraint.eval (booleanReceiptTrace own ctx lists log constants pub digests
      (keyAux accountId accessId fallback) (keyHeaderAux headerFallback)) 0 pos pub=0 := by
  let tr := booleanReceiptTrace own ctx lists log constants pub digests
    (keyAux accountId accessId fallback) (keyHeaderAux headerFallback)
  change keyZeroConstraint.eval tr 0 pos pub=0
  have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests
    (keyAux accountId accessId fallback) (keyHeaderAux headerFallback)
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply keyZero_constraint_off
    exact Or.inl (booleanReceiptTrace_padding own ctx lists log pos constants pub digests
      (keyAux accountId accessId fallback) (keyHeaderAux headerFallback) ha sVL)
  | some a =>
    have hstate := hc sVL (by decide)
    rw [ha] at hstate
    dsimp only at hstate
    by_cases hs : (eraseRow a).state=sVL
    · cases a with
      | header p row =>
        have hh := planned_header_state lists p row (List.mem_of_getElem? ha)
        change row.state=sVL at hs
        rw [hh] at hs
        contradiction
      | receipt p row =>
        change row.state=sVL at hs
        by_cases he : row.index+1=row.length
        · apply keyZero_constraint_off
          apply Or.inr
          have hf := hc fe (by decide)
          rw [ha] at hf
          simpa only [eraseRow,controlCell,idx,act,fs,fe,Nat.reduceEqDiff,ite_true,ite_false,he] using hf
        · have hi := planned_row_coord_bound lists (.receipt p row) (List.mem_of_getElem? ha)
          change row.index<row.length at hi
          have hl := planned_receipt_field_length lists p row (List.mem_of_getElem? ha)
          rw [hs] at hl
          change row.length=4 at hl
          have hn := planned_receipt_next lists pos p row ha (by omega)
          have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hn).1 hcap
          have hc1 := booleanReceiptTrace_planned_cell own ctx lists log (pos+1) constants pub digests
            (keyAux accountId accessId fallback) (keyHeaderAux headerFallback) _ hn kz (by decide)
          have h1 : tr.cell 0 (pos+1) kz=bitCell (keyZero (advance row)) :=
            hc1.trans (keyAux_transport accountId accessId constants pub digests (receiptPlanToken ctx lists) fallback p (advance row) kz (by decide))
          have hz : keyZero (advance row)=(row.index==0) := by
            cases row with
            | mk state i len =>
              dsimp only at hs hl hi he
              subst state len
              exact keyZero_next i (by omega)
          have hf := hc fs (by decide)
          rw [ha] at hf
          have hf' : tr.cell 0 pos fs=bitCell (row.index==0) := hf.trans (by
            change (if row.index=0 then (1:Fp) else 0)=bitCell (row.index==0)
            simp only [bitCell,beq_iff_eq])
          simp only [keyZeroConstraint,eval_mul3,eval_sub,eval_n,eval_c]
          change _ * _ * (tr.cell 0 ((pos+1)%2^log) kz-tr.cell 0 pos fs)=0
          rw [Nat.mod_eq_of_lt hpos,h1,hz,hf']
          grind only
    · apply keyZero_constraint_off
      exact Or.inl (hstate.trans (by rw [control_state _ (by decide),if_neg (Ne.symm hs)]))

end ZkFormal.NearV3.Assembly.RcptSkeleton
