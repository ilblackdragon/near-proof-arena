import ZkFormal.NearV3.Assembly.RcptNamedCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

def namedStartConstraints : List Expr :=
  [mul3 (c sV) (c fs) (sub (c acc) hexE),
   mul3 (c sV) (c fs) (sub (c vc0) (c b)),
   mul3 (c sV) (c fs) (sub (c vc1) (n b)),
   mul3 (c sV) (c fs) (sub (c h01) (.add hexE hexN))]

theorem namedStart_in_chars : ∀e∈namedStartConstraints,e∈cChars := by
  intro e he
  simp only [namedStartConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cChars,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem namedStart_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sV=0 ∨ tr.cell 0 pos fs=0) :
    ∀e∈namedStartConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [namedStartConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl <;> simp only [eval_mul3,eval_c]
  all_goals rcases hz with hz|hz <;> rw [hz] <;> grind only

set_option maxRecDepth 4096 in
theorem booleanReceiptTrace_namedStart (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈namedStartConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests
        (characterAux (namedAux fallback)) (characterHeaderAux headerFallback)) 0 pos pub=0 := by
  let tr := booleanReceiptTrace own ctx lists log constants pub digests
    (characterAux (namedAux fallback)) (characterHeaderAux headerFallback)
  change ∀e∈namedStartConstraints,e.eval tr 0 pos pub=0
  have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests
    (characterAux (namedAux fallback)) (characterHeaderAux headerFallback)
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply namedStart_zero
    exact Or.inl (booleanReceiptTrace_padding own ctx lists log pos constants pub digests
      (characterAux (namedAux fallback)) (characterHeaderAux headerFallback) ha sV)
  | some a =>
    have hstate := hc sV (by decide)
    rw [ha] at hstate
    dsimp only at hstate
    by_cases hs : (eraseRow a).state=sV
    · cases a with
      | header p row =>
        have hm := List.mem_of_getElem? ha
        rw [←plannedSegments_rows] at hm
        obtain ⟨seg,_,hm⟩ := List.mem_flatMap.mp hm
        obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
        have hh := (segment_member hc).1
        cases seg <;> cases he
        change row.state=sCL at hh
        simp only [eraseRow] at hs
        rw [hh] at hs
        contradiction
      | receipt p row =>
        change row.state=sV at hs
        by_cases hi : row.index=0
        · have hw' := planned_receipt_wf lists hw p row (List.mem_of_getElem? ha)
          have hl := planned_receipt_field_length lists p row (List.mem_of_getElem? ha)
          have hlen := characterBytes_bounds p.input hw' sV (by decide)
          have hn : row.index+1<row.length := by
            simp only [hl,hs,fieldLen,sV,sP,sCL,sPL,sVL,Nat.reduceEqDiff,↓reduceIte]
            change 2≤p.input.receipt.receiverId.length ∧ _ at hlen
            omega
          have hnext := planned_receipt_next lists pos p row ha hn
          have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hnext).1 hcap
          have ht : tr.height 0=2^log := rfl
          have hcell := booleanReceiptTrace_named_cells own ctx lists log pos constants pub digests fallback headerFallback p row ha
          have hbyte := booleanReceiptTrace_named_byte own ctx lists log pos constants pub digests fallback headerFallback p row ha hs
          have hnbyte := booleanReceiptTrace_named_byte own ctx lists log (pos+1) constants pub digests fallback headerFallback p (advance row) hnext hs
          have hhex := booleanReceiptTrace_named_hex own ctx lists log pos constants pub digests fallback headerFallback p row ha hs hw'
          have hnhex := booleanReceiptTrace_named_hex own ctx lists log (pos+1) constants pub digests fallback headerFallback p (advance row) hnext hs hw'
          have hhexN : hexN.eval tr 0 pos pub=Fp.ofNat (b2n (isHexC ((characterData p.input.receipt).recv.getD (row.index+1) 0))) := by
            simp only [hexN,eval_add,eval_n,ht,Nat.mod_eq_of_lt hpos]
            simpa only [hexE,eval_add,eval_c,advance] using hnhex
          intro e he
          simp only [namedStartConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
          rcases he with rfl|rfl|rfl|rfl
          all_goals
            simp only [eval_mul3,eval_sub,eval_add,eval_c,eval_n,ht,Nat.mod_eq_of_lt hpos,hbyte,hnbyte,hhex,hhexN]
            try rw [hnbyte]
            first | rw [hcell acc (by decide)] | rw [hcell vc0 (by decide)] | rw [hcell vc1 (by decide)] | rw [hcell h01 (by decide)]
            simp only [namedAux,hs,acc,vc0,vc1,h01,Nat.reduceEqDiff,↓reduceIte,advance,hi,Nat.zero_add,h01V,ofNat_add_e]
            have hh := named_score_start p.input.receipt
            grind only
        · apply namedStart_zero
          apply Or.inr
          have hf := hc fs (by decide)
          rw [ha] at hf
          simpa only [eraseRow,controlCell,idx,act,fs,fe,Nat.reduceEqDiff,↓reduceIte,hi] using hf
    · apply namedStart_zero
      apply Or.inl
      exact hstate.trans (by rw [control_state _ (by decide),if_neg (Ne.symm hs)])

end ZkFormal.NearV3.Assembly.RcptSkeleton
