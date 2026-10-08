import ZkFormal.NearV3.Assembly.RcptLedgerIndex

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

theorem planLists_prefix (lists : List (List Input)) (j r o2 : Nat)
    (p : ListPlan) (hp : p∈planLists j r o2 lists) :
    ∃ pre post, lists=pre++p.inputs::post ∧
      p.receiptIndex=r+pre.flatten.length := by
  induction lists generalizing j r o2 with
  | nil => simp [planLists] at hp
  | cons xs lists ih =>
    simp only [planLists,List.mem_cons] at hp
    rcases hp with he|hp
    · subst p
      exact ⟨[],lists,rfl,by simp⟩
    · obtain ⟨pre,post,hl,hi⟩ := ih (j+1) (r+xs.length)
        (o2+(xs.map refundLength).sum) hp
      refine ⟨xs::pre,post,by simp [hl],?_⟩
      simpa [Nat.add_assoc] using hi

/-- Actual receipt rows refer to the original flattened input at their global
index, including empty source lists and repeated-list occurrences. -/
theorem global_plan_receipt (lists : List (List Input)) (lp : ListPlan)
    (hl : lp∈planLists 0 0 8 lists) (p : ReceiptPlan)
    (hp : p∈planReceipts lp.listIndex lp.inputs.length lp.receiptIndex 1 12 lp.bodyOffset lp.lastList lp.inputs) :
    lists.flatten[p.receiptIndex]?=some p.input := by
  obtain ⟨pre,post,hls,hidx⟩ := planLists_prefix lists 0 0 8 lp hl
  obtain ⟨i,hi,hpi⟩ := planReceipts_index_input lp.inputs _ _ _ _ _ _ _ p hp
  have hib := (List.getElem?_eq_some_iff.mp hi).1
  subst lists
  simp only [Nat.zero_add] at hidx
  rw [hpi,hidx,List.flatten_append,List.flatten_cons]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hib]
  exact hi

def receiptPlanToken (ctx : ApplyCtx) (lists : List (List Input)) (p : ReceiptPlan) : TokenInput :=
  ⟨prefixBurn ctx (lists.flatten.map Input.receipt) 0 p.receiptIndex,nativeBurn ctx p.input.receipt⟩

/-- The constructor's token assignment at each generated receipt is exactly the
entry of the native ledger at that receipt's global index. -/
theorem receiptPlanToken_native (ctx : ApplyCtx) (lists : List (List Input)) (lp : ListPlan)
    (hl : lp∈planLists 0 0 8 lists) (p : ReceiptPlan)
    (hp : p∈planReceipts lp.listIndex lp.inputs.length lp.receiptIndex 1 12 lp.bodyOffset lp.lastList lp.inputs) :
    (tokenLedger ctx 0 (lists.flatten.map Input.receipt))[p.receiptIndex]?=
      some (receiptPlanToken ctx lists p) := by
  apply tokenLedger_get
  simp only [List.getElem?_map,global_plan_receipt lists lp hl p hp,Option.map_some]

/-- Native acceptance discharges the numeric bounds for every generated receipt
window; the renderer does not choose its running totals independently. -/
theorem applyNewChunk_plan_tokens (prims : Prims) (ctx : ApplyCtx) (t : PTrie)
    (lists : List (List Input)) (out : MainOut)
    (h : applyNewChunk prims ctx t (lists.flatten.map Input.receipt) = .ok out)
    (lp : ListPlan) (hl : lp∈planLists 0 0 8 lists) (p : ReceiptPlan)
    (hp : p∈planReceipts lp.listIndex lp.inputs.length lp.receiptIndex 1 12 lp.bodyOffset lp.lastList lp.inputs) :
    (receiptPlanToken ctx lists p).before < Params.two128 ∧
    (receiptPlanToken ctx lists p).before+(receiptPlanToken ctx lists p).burnt < Params.two128 := by
  have hh := (applyNewChunk_token_ledger prims ctx t _ out h).2.2
  exact hh _ (List.mem_of_getElem? (receiptPlanToken_native ctx lists lp hl p hp))

end ZkFormal.NearV3.Assembly.RcptSkeleton
