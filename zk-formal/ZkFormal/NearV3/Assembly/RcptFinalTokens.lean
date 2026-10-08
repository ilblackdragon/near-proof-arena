import ZkFormal.NearV3.Assembly.RcptFinalMetadata

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Final physical token bytes are the actual successful native execution
result, including the empty-receipt and terminal-empty-list cases. -/
theorem booleanReceiptTrace_final_tokens (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length<2^log)
    (hl : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos lastR≠0)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (i : Nat) (hi : i<16) :
    (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos (tok i)=
      Fp.ofNat (((u128 out.tokensBurnt).getD i 0).toNat) := by
  obtain ⟨a,ha,hlast⟩ := booleanReceiptTrace_lastR_position own ctx lists hw log pos constants pub digests fallback headerFallback hcap hl
  rw [←entityPlans_rows] at hlast
  obtain ⟨p,hp,hpa⟩ := flatMap_last_nonempty EntityPlan.rows (entityPlans lists) a
    (fun p _=>p.rows_nonempty) hlast
  have hpm := List.mem_of_getLast? hp
  obtain ⟨hn,_⟩ := entityPlans_final_totals lists p hp
  have hout := (applyNewChunk_token_ledger prims ctx t _ out hrun).1
  have hfull : prefixBurn ctx (lists.flatten.map Input.receipt) 0 lists.flatten.length=out.tokensBurnt := by
    simp only [prefixBurn]
    rw [List.take_of_length_le (by simp only [List.length_map];omega),Nat.zero_add]
    exact hout.symm
  rw [booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback a ha (tok i)
    (by change decide (31≤95+i ∧ 95+i≤42)=false;simp only [decide_eq_false_iff_not];omega)]
  cases p with
  | header lp =>
    have he := EntityPlan.header_last lp a hpa
    subst a
    change headerCell _ lp _ (tok i)=_
    rw [header_stream_token _ _ _ _ _ _ hi]
    have hb : headerBurn ctx (lists.flatten.map Input.receipt) lp=prefixBurn ctx (lists.flatten.map Input.receipt) 0 lp.receiptIndex := by simp only [headerBurn,prefixBurn,Nat.zero_add]
    rw [hb]
    have hn' : lp.receiptIndex=lists.flatten.length := by simpa [EntityPlan.receiptIndex,EntityPlan.isHeader] using hn
    rw [hn',hfull]
  | receipt rp =>
    obtain ⟨row,hs,_,he⟩ := EntityPlan.receipt_last rp (entityPlans_receipt_wf lists hw rp hpm) a hpa
    subst a
    change receiptCell _ _ rp row (tok i)=_
    rw [receipt_token_cell _ _ _ _ _ _ _ i hi]
    have hrow : row=⟨finalState rp.input,row.index,row.length⟩ := by cases row;simp_all
    rw [hrow,tokenOf_final]
    have hr : (lists.flatten.map Input.receipt)[rp.receiptIndex]?=some rp.input.receipt := by
      rw [←plannedSegments_rows] at ha
      have hm := List.mem_of_getElem? ha
      obtain ⟨seg,hseg,hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨r,_,he⟩ := List.mem_map.mp hm
      cases seg with
      | header => cases he
      | receipt p s => cases he;exact plannedSegment_receipt_input lists rp s hseg
    simp only [TokenInput.newBytes,receiptPlanToken]
    rw [←prefixBurn_succ ctx _ 0 _ _ hr]
    have hn' : rp.receiptIndex+1=lists.flatten.length := hn
    rw [hn',hfull]

end ZkFormal.NearV3.Assembly.RcptSkeleton
