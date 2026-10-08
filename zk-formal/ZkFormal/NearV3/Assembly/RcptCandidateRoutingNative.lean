import ZkFormal.NearV3.Assembly.RcptCandidateRoutingPredecessor
import ZkFormal.NearV3.Assembly.RcptCandidateNativeTable

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open RoutingQCandidate

theorem booleanReceiptTrace_native_q_bound {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hd : decodeStateWitness bs=.ok w)
    (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hls : lists.flatten.map Input.receipt=appliedReceipts k w)
    (accountId : ReceiptPlan→Nat) (constants : ReceiptPlan→Nat→Fp)
    (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (aux : ReceiptPlan→Coord→Nat→Fp) (headers : ListPlan→Coord→Nat→Fp) (log pos : Nat)
    (hs : startsReceiver (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId constants) pub digests aux headers) 0 pos) :
    cv (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId constants) pub digests aux headers) 0 pos q<128 := by
  let cn := completeReceiptConstants ctx k accountId constants
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    have hz := booleanReceiptTrace_padding own ctx lists log pos cn pub digests aux headers ha sV
    have h1 := hs.1
    rw [hz] at h1
    exact False.elim (fp_zero_ne_one h1)
  | some a =>
    have hc := booleanReceiptTrace_planned_cell own ctx lists log pos cn pub digests aux headers a ha
    cases a with
    | header rp row =>
      have hrow := planned_header_state lists rp row (List.mem_of_getElem? ha)
      have hz : (booleanReceiptTrace own ctx lists log cn pub digests aux headers).cell 0 pos sV=0 := by
        apply (hc sV (by decide)).trans
        change (if sV=row.state then (1:Fp) else 0)=0
        rw [hrow];rfl
      exact False.elim (fp_zero_ne_one (hz.symm.trans hs.1))
    | receipt rp row =>
      have hmem := planned_receipt_input_mem lists rp row (List.mem_of_getElem? ha)
      have hlt := (native_routing_selected hp hk hd rp (by
        rw [←hls];exact List.mem_map.mpr ⟨rp.input,hmem,rfl⟩)).1
      have hcell : (booleanReceiptTrace own ctx lists log cn pub digests aux headers).cell 0 pos q=
          Fp.ofNat (nativeRoutingIndex k rp.input.receipt) := by
        apply (hc q (by decide)).trans
        rfl
      change ((booleanReceiptTrace own ctx lists log cn pub digests aux headers).cell 0 pos q).toNat<128
      rw [hcell,Fp.toNat_ofNat]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hlt

end ZkFormal.NearV3.Assembly.RcptSkeleton
