import ZkFormal.NearV3.Candidates.NativeAccessKeyView
namespace ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly Assembly.RcptSkeleton RcptV3 RcptV3Proof

theorem physical_messages (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (pre : PTrie) (hw:∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh:2^log<Algebra.P) :
    let rs:=lists.flatten.map Input.receipt
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests
      (completeReceiptAux ctx k lists accountId (NativeReceiptAccessIds.accessId pre)
        (depositFinalAux previous accounts (rankAux pre rs fallback))) headerFallback) 0
    ∀(hL:TableLocal receiptArithmeticCandidate tr 0 pub) (bs : List ListBlock) (e : Nat),
      ListChain tr 0 0 bs e→∀sd,
      (List.range (tr.height 0)).flatMap (fun pos=>rowTraffic RcptV3.interactions tr 0 pos pub B_AKC sd)=
        (eventMessages pre rs sd).map Msg.toFp := by
  intro rs tr hL bs e hc sd
  have hf:=canonical_native_views own ctx lists log constants pub digests _ headerFallback hw hh hL bs e hc
  rw [ReceiptCandidateProof.ListChain.access_counter_traffic hL hc sd,access_view_flat,hf]
  have hm:((locatedViews tr lists).flatMap (ReceiptCandidateProof.accessCounterMsgs sd 0)).map Msg.toFp=
      ((receiptLocations 0 (entityPlans lists)).flatMap (fun x=>receiptMessages pre rs x.2 sd)).map Msg.toFp := by
    simp only [locatedViews,List.flatMap_map,List.map_flatMap]
    apply ZkFormal.Near.Render.flatMap_congr'
    intro x hx
    have lay:=canonical_location_layout own ctx lists log constants pub digests _ headerFallback hw hh hL bs e hc x.1 x.2 hx
    have hg:=ReceiptCandidateProof.Layout.access_counter hL lay sd
    have hwindows:=ReceiptCandidateProof.Layout.akc_window hL lay sd
    rw [hwindows] at hg
    obtain ⟨before,after,hb,hoff⟩:=native_locations_block lists x.1 x.2 hx
    have hi:((plannedRows lists)[x.1+(40+x.2.input.receipt.predecessorId.length+x.2.input.receipt.receiverId.length)]?)=
        some (.receipt x.2 ⟨sT0,0,1⟩):=by
      rw [hoff,hb,List.append_assoc,List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp (receipt_t0_position x.2)).1,receipt_t0_position]
    have hr:=physical_row own ctx k lists log _ constants pub digests accountId previous accounts fallback headerFallback pre rs x.2 hi sd
    exact hg.symm.trans hr
  rw [hm,located_messages]
end ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
