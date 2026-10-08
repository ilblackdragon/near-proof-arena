import ZkFormal.NearV3.Assembly.RcptCanonicalNativeViews
namespace ZkFormal.NearV3.Candidates
open NearSpec NearSpecV3 ZkFormal.Near Assembly Assembly.RcptSkeleton ZkFormal.Air ZkFormal.Algebra RcptV3Proof

theorem location_entity (es : List EntityPlan) (start off : Nat) (p : ReceiptPlan)
    (h:(off,p)∈receiptLocations start es) :
    DecodedEntity.receipt (inputShape off p.input)∈nativeEntities start es := by
  induction es generalizing start with
  | nil=>simp [receiptLocations] at h
  | cons e es ih=>
    cases e with
    | header lp=>
      exact List.mem_cons_of_mem _ (ih _ h)
    | receipt rp=>
      rcases List.mem_cons.mp h with hh|hh
      · cases hh;exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ hh)

theorem canonical_location_layout (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw:∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh:2^log<Algebra.P)
    (hL:TableLocal receiptArithmeticCandidate (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc:ListChain (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 0 bs e)
    (off : Nat) (p : ReceiptPlan) (hp:(off,p)∈receiptLocations 0 (entityPlans lists)) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0
    let y:=inputShape off p.input
    Layout tr 0 y.s y.h y.Lp y.Lv y.Ls y.kt := by
  have hs:=decoded_native_sequence own ctx lists log constants pub digests fallback headerFallback hw hh hL
    _ e (ListChain.decoded hc) (ReceiptCandidateProof.ListChain.end_padding hc).2
  have hm:=location_entity (entityPlans lists) 0 off p hp
  rw [←hs] at hm
  obtain ⟨B,hB,hy⟩:=List.mem_flatMap.mp hm
  simp only [ListBlock.entities,List.mem_cons,List.mem_map] at hy
  rcases hy with hy|⟨y,hy,he⟩
  · cases hy
  · cases he
    exact (hc.blocks B hB).layouts _ hy
end ZkFormal.NearV3.Candidates
