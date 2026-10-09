import ZkFormal.NearV3.Assembly.RcptNativePlanOrder

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

/-- Executable receipt locations; headers contribute their physical row count
but emit no receipt location. No equality test or deduplication is used. -/
def receiptLocations (start : Nat) : List EntityPlan→List (Nat×ReceiptPlan)
  | []=>[]
  | .header p::es=>receiptLocations (start+(EntityPlan.header p).rows.length) es
  | .receipt p::es=>(start,p)::receiptLocations (start+(plannedReceiptRows p).length) es

theorem receiptLocations_inputs (es : List EntityPlan) (start : Nat) :
    (receiptLocations start es).map (fun x=>x.2.input)=es.filterMap EntityPlan.input? := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih => cases e <;> simp only [receiptLocations,List.map_cons,List.filterMap_cons,EntityPlan.input?,ih]

theorem receiptLocations_block (es : List EntityPlan) (start off : Nat) (p : ReceiptPlan)
    (hm : (off,p)∈receiptLocations start es) :
    ∃pre post : List PlannedRow, es.flatMap EntityPlan.rows=pre++plannedReceiptRows p++post ∧
      off=start+pre.length := by
  induction es generalizing start with
  | nil => simp [receiptLocations] at hm
  | cons e es ih =>
    cases e with
    | header lp =>
      obtain ⟨pre,post,he,ho⟩ := ih _ hm
      refine ⟨(EntityPlan.header lp).rows++pre,post,?_,?_⟩
      · simpa only [List.flatMap_cons,he,List.append_assoc]
      · simp only [List.length_append];omega
    | receipt rp =>
      simp only [receiptLocations,List.mem_cons] at hm
      rcases hm with he|hm
      · cases he
        exact ⟨[],es.flatMap EntityPlan.rows,rfl,by simp⟩
      · obtain ⟨pre,post,he,ho⟩ := ih _ hm
        refine ⟨plannedReceiptRows rp++pre,post,?_,?_⟩
        · simpa only [List.flatMap_cons,EntityPlan.rows,he,List.append_assoc]
        · simp only [List.length_append];omega

theorem native_locations_block (lists : List (List Input)) (off : Nat) (p : ReceiptPlan)
    (hm : (off,p)∈receiptLocations 0 (entityPlans lists)) :
    ∃pre post : List PlannedRow, plannedRows lists=pre++plannedReceiptRows p++post ∧ off=pre.length := by
  obtain ⟨pre,post,hp,ho⟩ := receiptLocations_block _ _ _ _ hm
  exact ⟨pre,post,by simpa only [entityPlans_rows] using hp,by simpa using ho⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
