import ZkFormal.NearV3.Assembly.RcptDepositIdle

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem booleanReceiptTrace_candidateDeposit (own : Nat) (ctx : ApplyCtx)
    (lists : List (List Input))
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (hdata : ∀p row,PlannedRow.receipt p row∈plannedRows lists→DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt))
    (hindex : ∀p row,PlannedRow.receipt p row∈plannedRows lists→p.receiptIndex<4481)
    (hprevious : ∀p row,PlannedRow.receipt p row∈plannedRows lists→previous p≤p.receiptIndex)
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈depositAgeConstraints,e.eval
      (booleanReceiptTrace own ctx lists log (depositConstants accounts (depositAgeConstants previous constants))
        pub digests (depositAgeAux previous (depositAux accounts fallback)) (depositHeaderAux headerFallback)) 0 pos pub=0 := by
  let cn := depositConstants accounts (depositAgeConstants previous constants)
  let aux := depositAgeAux previous (depositAux accounts fallback)
  let headers := depositHeaderAux headerFallback
  let tr := booleanReceiptTrace own ctx lists log cn pub digests aux headers
  change ∀e∈depositAgeConstraints,e.eval tr 0 pos pub=0
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply depositCandidate_inactive
    · exact booleanReceiptTrace_padding own ctx lists log pos cn pub digests aux headers ha sDEP
    · exact booleanReceiptTrace_padding own ctx lists log pos cn pub digests aux headers ha r1
    · exact booleanReceiptTrace_padding own ctx lists log pos cn pub digests aux headers ha st
  | some a =>
    have hc := booleanReceiptTrace_planned_cell own ctx lists log pos cn pub digests aux headers a ha
    cases a with
    | header p row =>
      have hs := planned_header_state lists p row (List.mem_of_getElem? ha)
      apply depositCandidate_inactive
      · apply (hc sDEP (by decide)).trans
        change (if sDEP=row.state then (1:Fp) else 0)=0
        rw [hs];rfl
      · exact (hc r1 (by decide)).trans (deposit_header_idle own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback p row).1
      · exact (hc st (by decide)).trans (deposit_header_idle own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback p row).2
    | receipt p row =>
      have hdata' := hdata p row (List.mem_of_getElem? ha)
      have hindex' := hindex p row (List.mem_of_getElem? ha)
      have hprevious' := hprevious p row (List.mem_of_getElem? ha)
      by_cases hs : row.state=sDEP
      · have hi := planned_row_coord_bound lists _ (List.mem_of_getElem? ha)
        have hl := planned_receipt_field_length lists p row (List.mem_of_getElem? ha)
        rw [hs] at hl
        change row.length=16 at hl
        cases row with
        | mk state i len =>
          dsimp only at hs hl hi
          subst state len
          change i<16 at hi
          by_cases he : i+1=16
          · have hi15 : i=15 := by omega
            subst i
            let pair := receiptPair (booleanConstants cn)
              (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux aux)) p ⟨sDEP,15,16⟩ ⟨sDEP,15,16⟩
            intro e he
            rw [depositCandidate_last_eval_agree tr pair 0 pos 0 0 pub
              (fun col hh=>hc col (depositCandidate_no_emission col hh)) rfl e he]
            exact receipt_deposit_candidate_local previous accounts constants pub digests (receiptPlanToken ctx lists)
              fallback p 15 (by decide) ⟨sDEP,15,16⟩ (fun h=>by omega) hdata' hindex' hprevious' e he
          · have hin : i+1<16 := by omega
            have hn := planned_receipt_next lists pos p ⟨sDEP,i,16⟩ ha hin
            have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hn).1 hcap
            have hnc := booleanReceiptTrace_planned_cell own ctx lists log (pos+1) cn pub digests aux headers _ hn
            let pair := receiptPair (booleanConstants cn)
              (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux aux)) p ⟨sDEP,i,16⟩ ⟨sDEP,i+1,16⟩
            intro e he
            rw [depositCandidate_eval_agree tr pair 0 pos 0 0 pub
              (fun col hh=>hc col (depositCandidate_no_emission col hh)) ?_ e (List.all_eq_true.mp depositCandidate_footprint e he)]
            · exact receipt_deposit_candidate_local previous accounts constants pub digests (receiptPlanToken ctx lists)
                fallback p i hi ⟨sDEP,i+1,16⟩ (fun _=>rfl) hdata' hindex' hprevious' e he
            · intro col hh
              change tr.cell 0 ((pos+1)%2^log) col=_
              rw [Nat.mod_eq_of_lt hpos]
              exact hnc col (depositCandidate_no_emission col (deposit_next_current col hh))
      · apply depositCandidate_inactive
        · apply (hc sDEP (by decide)).trans
          exact (receipt_control_cell (booleanConstants cn)
            (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux aux)) p row (show controlColumn sDEP=true by decide)).trans
            ((control_state row (show sDEP∈states by decide)).trans (if_neg (Ne.symm hs)))
        · exact (hc r1 (by decide)).trans (deposit_receipt_idle previous accounts cn pub digests
            (receiptPlanToken ctx lists) fallback p row hs).1
        · exact (hc st (by decide)).trans (deposit_receipt_idle previous accounts cn pub digests
            (receiptPlanToken ctx lists) fallback p row hs).2

end ZkFormal.NearV3.Assembly.RcptSkeleton
