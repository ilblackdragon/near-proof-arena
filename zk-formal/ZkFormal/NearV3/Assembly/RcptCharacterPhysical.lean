import ZkFormal.NearV3.Assembly.RcptCharacterZero

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render.RcptP

theorem character_eval_string (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (ch s : Nat) (hc : ch<256) (hv : vch ch=true) (hs : s∈[sP,sV,sS])
    (hcells : ∀col,chCol col=true→tr.cell 0 pos col=chRow ch s col) :
    ∀e∈charLocalConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  have hf := List.all_eq_true.mp charLocalConstraints_shape.2.1 e he
  have hf' := hf
  simp only [charLoc,Bool.and_eq_true,List.all_eq_true,List.isEmpty_iff] at hf'
  obtain ⟨⟨hcur,hnx⟩,hno⟩ := hf'
  rw [eval_evR,evR_noPS e hno,evR_congr (cur':=chRow ch s) (nx':=fun _=>0) e
    (fun col hcol=>hcells col (hcur col hcol)) (fun col hcol=>by rw [hnx] at hcol;cases hcol)]
  exact charLocalConstraints_string ch s hc hv hs e he

theorem character_eval_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hcells : ∀col,characterZeroColumn col=true→tr.cell 0 pos col=0) :
    ∀e∈charLocalConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  rw [eval_evR]
  exact Zr_sound hcells (fun _ h=>by cases h) (fun h=>by cases h) e
    (List.all_eq_true.mp charLocalConstraints_zero_shape e he)

set_option maxRecDepth 4096 in
theorem character_columns_noEmission :
    (∀col,chCol col=true→emissionColumn col=false) ∧
    (∀col,characterZeroColumn col=true→emissionColumn col=false) := by
  constructor <;> intro col hc
  · simp only [chCol,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hc
    change decide (31≤col ∧ col≤42)=false
    simp only [decide_eq_false_iff_not]
    omega
  · simp only [characterZeroColumn,sP,sV,sS,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at hc
    change decide (31≤col ∧ col≤42)=false
    simp only [decide_eq_false_iff_not]
    omega

theorem booleanReceiptTrace_characters (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈charLocalConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests (characterAux fallback)
        (characterHeaderAux headerFallback)) 0 pos pub=0 := by
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    exact character_eval_zero _ pos pub (fun col _=>booleanReceiptTrace_padding own ctx lists log pos constants pub digests
      (characterAux fallback) (characterHeaderAux headerFallback) ha col)
  | some a =>
    have hm := List.mem_of_getElem? ha
    rw [←plannedSegments_rows] at hm
    obtain ⟨seg,hseg,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨row,hrow,he⟩ := List.mem_map.mp hm
    obtain ⟨hs,hi,hlen⟩ := segment_member hrow
    subst a
    have hcell (col : Nat) (hc : emissionColumn col=false) :=
      booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
        (characterAux fallback) (characterHeaderAux headerFallback) _ ha col hc
    cases seg with
    | header p =>
      change row.state=sCL at hs
      change row.length=12 at hlen
      cases row with
      | mk state i len =>
        dsimp only at hs hlen
        subst state len
        apply character_eval_zero
        intro col hc
        rw [hcell col (character_columns_noEmission.2 col hc)]
        exact character_header_cells own _ headerFallback p i col hc
    | receipt p s =>
      have hw' := planned_receipt_wf lists hw p row (List.mem_of_getElem? ha)
      by_cases hstr : row.state∈[sP,sV,sS]
      · have hidx : row.index<fieldLen p.input row.state := by
          change row.state=s at hs
          change row.length=fieldLen p.input s at hlen
          rw [hs]
          exact hi
        apply character_eval_string _ pos pub (characterByte p row) row.state
          (characterByte_lt p row) (characterByte_valid p row hw' hstr hidx) hstr
        intro col hc
        rw [hcell col (character_columns_noEmission.1 col hc)]
        exact character_receipt_cells ctx lists constants pub digests fallback p row hstr col hc
      · apply character_eval_zero
        intro col hc
        rw [hcell col (character_columns_noEmission.2 col hc)]
        exact character_receipt_nonstring ctx lists constants pub digests fallback p row hstr col hc

end ZkFormal.NearV3.Assembly.RcptSkeleton
