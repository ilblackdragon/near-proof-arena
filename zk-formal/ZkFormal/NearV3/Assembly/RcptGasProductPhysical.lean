import ZkFormal.NearV3.Assembly.RcptGasProductEndpoint

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem booleanReceiptTrace_nativeGasProduct (own : Nat) (ctx : ApplyCtx)
    (lists : List (List Input))
    (hprice : ∀xs∈lists,∀x∈xs,x.receipt.gasPrice<256^16)
    (hburn : ∀xs∈lists,∀x∈xs,nativeBurn ctx x.receipt<256^16)
    (hsurplus : ∀xs∈lists,∀x∈xs,nativeRefundAmount ctx x.receipt<256^16)
    (hp : ctx.gasPrice<256^16)
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈gasProductConstraints systemSurplus,e.eval
      (booleanReceiptTrace own ctx lists log (gasEffectiveConstants ctx constants)
        pub digests (nativeGasProductAux ctx (receiptPlanToken ctx lists) fallback) headerFallback) 0 pos pub=0 := by
  let cn := gasEffectiveConstants ctx constants
  let aux := nativeGasProductAux ctx (receiptPlanToken ctx lists) fallback
  let tr := booleanReceiptTrace own ctx lists log cn pub digests aux headerFallback
  change ∀e∈gasProductConstraints systemSurplus,e.eval tr 0 pos pub=0
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply gasProduct_inactive
    exact booleanReceiptTrace_padding own ctx lists log pos cn pub digests aux headerFallback ha sGP
  | some a =>
    have hc := booleanReceiptTrace_planned_cell own ctx lists log pos cn pub digests aux headerFallback a ha
    cases a with
    | header p row =>
      have hs := planned_header_state lists p row (List.mem_of_getElem? ha)
      apply gasProduct_inactive
      apply (hc sGP (by decide)).trans
      change (if sGP=row.state then (1:Fp) else 0)=0
      rw [hs];rfl
    | receipt p row =>
      obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp (planned_receipt_input_mem lists p row (List.mem_of_getElem? ha))
      have hprice' := hprice xs hxs p.input hx
      have hburn' := hburn xs hxs p.input hx
      have hsurplus' := hsurplus xs hxs p.input hx
      by_cases hs : row.state=sGP
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
              (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux aux)) p ⟨sGP,15,16⟩ ⟨sGP,15,16⟩
            intro e he
            rw [gasProduct_last_eval_agree tr pair 0 pos 0 0 pub
              (fun col hh=>hc col (gasProduct_no_emission col hh)) rfl e he]
            exact receipt_gasProduct_local ctx constants pub digests (receiptPlanToken ctx lists)
              fallback p 15 (by decide) ⟨sGP,15,16⟩ (fun h=>by omega) hprice' hp rfl hburn' hsurplus' e he
          · have hin : i+1<16 := by omega
            have hn := planned_receipt_next lists pos p ⟨sGP,i,16⟩ ha hin
            have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hn).1 hcap
            have hnc := booleanReceiptTrace_planned_cell own ctx lists log (pos+1) cn pub digests aux headerFallback _ hn
            let pair := receiptPair (booleanConstants cn)
              (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux aux)) p ⟨sGP,i,16⟩ ⟨sGP,i+1,16⟩
            intro e he
            rw [gasProduct_eval_agree tr pair 0 pos 0 0 pub
              (fun col hh=>hc col (gasProduct_no_emission col hh)) ?_ e (List.all_eq_true.mp gasProduct_footprint e he)]
            · exact receipt_gasProduct_local ctx constants pub digests (receiptPlanToken ctx lists)
                fallback p i hi ⟨sGP,i+1,16⟩ (fun _=>rfl) hprice' hp rfl hburn' hsurplus' e he
            · intro col hh
              change tr.cell 0 ((pos+1)%2^log) col=_
              rw [Nat.mod_eq_of_lt hpos]
              have hcol : gasProductColumn col=true := by
                simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
                rcases hh with rfl|rfl <;> decide
              exact hnc col (gasProduct_no_emission col hcol)
      · apply gasProduct_inactive
        apply (hc sGP (by decide)).trans
        exact (receipt_control_cell (booleanConstants cn)
          (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux aux)) p row (show controlColumn sGP=true by decide)).trans
          ((control_state row (show sGP∈states by decide)).trans (if_neg (Ne.symm hs)))

end ZkFormal.NearV3.Assembly.RcptSkeleton
