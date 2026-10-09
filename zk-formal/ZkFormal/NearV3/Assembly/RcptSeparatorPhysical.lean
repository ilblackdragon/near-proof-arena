import ZkFormal.NearV3.Assembly.RcptSeparatorCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render.RcptP

theorem booleanReceiptTrace_noString (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (a : PlannedRow) (ha : (plannedRows lists)[pos]?=some a)
    (hs : (eraseRow a).state∉[sP,sV,sS]) :
    SS.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback
  have hp := hc sP (by decide)
  have hv := hc sV (by decide)
  have hsig := hc sS (by decide)
  rw [ha] at hp hv hsig
  dsimp only at hp hv hsig
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  have hn : sP≠(eraseRow a).state ∧ sV≠(eraseRow a).state ∧ sS≠(eraseRow a).state := by omega
  have hp' : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos sP=0 := by
    rw [hp,control_state _ (by decide),if_neg hn.1]
  have hv' : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos sV=0 := by
    rw [hv,control_state _ (by decide),if_neg hn.2.1]
  have hs' : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos sS=0 := by
    rw [hsig,control_state _ (by decide),if_neg hn.2.2]
  simp only [SS,sum,eval_add,eval_c,hp',hv',hs']
  change (0:Fp)+(0+(0+0))=0
  grind only

theorem booleanReceiptTrace_separators (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈separatorConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests (characterAux fallback)
        (characterHeaderAux headerFallback)) 0 pos pub=0 := by
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply separator_current_zero
    apply Or.inr
    simp only [sepE,eval_add,eval_c,
      booleanReceiptTrace_padding own ctx lists log pos constants pub digests (characterAux fallback)
        (characterHeaderAux headerFallback) ha]
    grind only
  | some a =>
    have hm := List.mem_of_getElem? ha
    rw [←plannedSegments_rows] at hm
    obtain ⟨seg,hseg,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨row,hrow,he⟩ := List.mem_map.mp hm
    obtain ⟨hs,hi,hlen⟩ := segment_member hrow
    subst a
    cases seg with
    | header p =>
      apply separator_current_zero
      exact Or.inl (booleanReceiptTrace_noString own ctx lists log pos constants pub digests (characterAux fallback)
        (characterHeaderAux headerFallback) _ ha (by change row.state∉[sP,sV,sS];change row.state=sCL at hs;rw [hs];decide))
    | receipt p s =>
      have hw' := planned_receipt_wf lists hw p row (List.mem_of_getElem? ha)
      have hlen' : row.length=fieldLen p.input row.state := by
        change row.state=s at hs
        change row.length=fieldLen p.input s at hlen
        rw [hs];exact hlen
      have hi' : row.index<fieldLen p.input row.state := by change row.index<fieldLen p.input s at hi;change row.state=s at hs;rw [hs];exact hi
      by_cases hstr : row.state∈[sP,sV,sS]
      · have hsep := booleanReceiptTrace_separator own ctx lists log pos constants pub digests fallback headerFallback p row ha hw' hstr hi'
        cases hb : sepB (characterByte p row) with
        | false =>
          apply separator_current_zero
          exact Or.inr (by simpa only [hb,bitCell,Bool.false_eq_true,ite_false] using hsep)
        | true =>
          obtain ⟨hf,hn,hnext⟩ := characterByte_separator p row hw' hstr hi' hb
          have hnextrow := planned_receipt_next lists pos p row ha (by omega)
          have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hnextrow).1 hcap
          have hsepnext := booleanReceiptTrace_separator own ctx lists log (pos+1) constants pub digests fallback headerFallback p (advance row) hnextrow hw' hstr hn
          have hsn : sepN.eval (booleanReceiptTrace own ctx lists log constants pub digests (characterAux fallback)
              (characterHeaderAux headerFallback)) 0 pos pub=0 := by
            have ht : (booleanReceiptTrace own ctx lists log constants pub digests (characterAux fallback)
              (characterHeaderAux headerFallback)).height 0=2^log := rfl
            simp only [sepN,eval_add,eval_n,ht,Nat.mod_eq_of_lt hpos]
            simpa only [sepE,eval_add,eval_c,hnext,bitCell,Bool.false_eq_true,ite_false] using hsepnext
          have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests (characterAux fallback) (characterHeaderAux headerFallback)
          have hfs := hc fs (by decide)
          have hfe := hc fe (by decide)
          rw [ha] at hfs hfe
          have hfs' : (booleanReceiptTrace own ctx lists log constants pub digests (characterAux fallback) (characterHeaderAux headerFallback)).cell 0 pos fs=0 := by
            simpa only [SegmentPlan.wrap,eraseRow,controlCell,act,idx,fs,fe,Nat.reduceEqDiff,↓reduceIte,hf] using hfs
          have hfe' : (booleanReceiptTrace own ctx lists log constants pub digests (characterAux fallback) (characterHeaderAux headerFallback)).cell 0 pos fe=0 := by
            have hh : ¬row.index+1=row.length := by omega
            simpa only [SegmentPlan.wrap,eraseRow,controlCell,act,idx,fs,fe,Nat.reduceEqDiff,↓reduceIte,hh] using hfe
          intro e he
          simp only [separatorConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
          rcases he with rfl|rfl|rfl <;> simp only [eval_mul,eval_mul3,eval_c,hsn,hfs',hfe'] <;> grind only
      · apply separator_current_zero
        exact Or.inl (booleanReceiptTrace_noString own ctx lists log pos constants pub digests (characterAux fallback)
          (characterHeaderAux headerFallback) _ ha hstr)

end ZkFormal.NearV3.Assembly.RcptSkeleton
