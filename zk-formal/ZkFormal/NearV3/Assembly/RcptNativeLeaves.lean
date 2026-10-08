import ZkFormal.NearV3.Assembly.RcptNativeLocations

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- Views are read from the actual physical trace at executable receipt offsets.
Their being the canonical local extractor's ListChain remains a separate bridge. -/
def locatedViews (tr : Trace Fp) (lists : List (List Input)) : List RcptE :=
  (receiptLocations 0 (entityPlans lists)).map fun x=>rcptOf tr 0 (inputShape x.1 x.2.input)

theorem native_leaves (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hid : ∀x∈lists.flatten,x.receipt.receiptId.length=32) :
    (locatedViews (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (outcomeDigests ctx digests)
        fallback headerFallback) 0) lists).map (fun x=>x.leaf)=
      lists.flatten.map (fun x=>(u32 2++(nativeOutcome ctx x.receipt).id++
        sha256 (nativeOutcome ctx x.receipt).partialEncode).map UInt8.toNat) := by
  have hi := receiptLocations_inputs (entityPlans lists) 0
  rw [entityPlans_inputs] at hi
  rw [←hi,List.map_map]
  unfold locatedViews
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  obtain ⟨pre,post,hb,ho⟩ := native_locations_block lists x.1 x.2 hx
  have hm : x.2.input∈lists.flatten := by
    rw [←hi]
    exact List.mem_map.mpr ⟨x,hx,rfl⟩
  dsimp only [Function.comp_def]
  rw [ho]
  exact native_leaf own ctx lists log constants pub digests fallback headerFallback x.2 pre post hb (hid _ hm)

theorem executed_leaves (prims : Prims) (own : Nat) (ctx : ApplyCtx) (t : PTrie)
    (lists : List (List Input)) (out : MainOut)
    (hex : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hid : ∀x∈lists.flatten,x.receipt.receiptId.length=32) :
    (locatedViews (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (outcomeDigests ctx digests)
        fallback headerFallback) 0) lists).map (fun x=>x.leaf)=
      out.outcomes.map (fun o=>(u32 2++o.id++sha256 o.partialEncode).map UInt8.toNat) := by
  rw [native_leaves own ctx lists log constants pub digests fallback headerFallback hid,
    applyNewChunk_outcomes prims hex,List.map_map,List.map_map]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
