import ZkFormal.NearV3.Assembly.RoutingSelection
import ZkFormal.NearV3.Assembly.ReceiptWellformed

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3

theorem applied_receipt_routed {k : WalkD0} {w : StateWitness} {r : Receipt}
    (h : r∈appliedReceipts k w) : k.L.shardOf r.receiverId=k.H.shardId := by
  rw [appliedReceipts_eq_flatMap] at h
  obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp h
  unfold blockApplied at hb
  obtain ⟨rs,hrs,hr⟩ := List.mem_flatten.mp hb
  obtain ⟨e,_,he⟩ := List.mem_map.mp hrs
  subst rs
  simpa only [beq_iff_eq] using (List.mem_filter.mp hr).2

/-- Successful witness decoding supplies account length; native application
supplies routing. Neither is an independent assumption on the constructor. -/
theorem applied_receipt_selection {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    (hw : decodeStateWitness bs=.ok w) {r : Receipt} (hr : r∈appliedReceipts k w) :
    ∃q,selectInterval k.L k.H.shardId r.receiverId=some q ∧ q<128 ∧
      inInterval r.receiverId ((boundedPrep p k.L k.H.shardId).bnds.getD q (none,none))=true ∧
      ∀pos,pos≤r.receiverId.length → routeKey (boundedPrep p k.L k.H.shardId).bnds q pos∈
        Public.boundaryRecords (boundedPrep p k.L k.H.shardId) := by
  have hwf := appliedReceipts_wf hw r hr
  have hlen : r.receiverId.length≤64 := by
    simp only [Receipt.wf,AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hwf
    grind only
  exact selected_requests_covered hp hk r.receiverId (applied_receipt_routed hr) hlen

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
