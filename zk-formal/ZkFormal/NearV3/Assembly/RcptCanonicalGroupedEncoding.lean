import ZkFormal.NearV3.Assembly.RcptEncodingTokens

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

variable (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)

private abbrev nativeTrace := RoutingQCandidate.patchTrace
  (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0

include hw in
private theorem native_entities_encoding (es pre : List EntityPlan)
    (he : entityPlans lists=pre++es) :
    (nativeEntities (pre.flatMap EntityPlan.rows).length es).map
      (decodedEncodingToken (nativeTrace own ctx lists log constants pub digests fallback headerFallback))=
      es.map nativeEncodingToken := by
  induction es generalizing pre with
  | nil => rfl
  | cons p es ih =>
    simp only [nativeEntities,List.map_cons]
    have hei : entityPlans lists=(pre++[p])++es := by simpa only [List.append_assoc,List.singleton_append] using he
    have ht := ih (pre++[p]) hei
    simp only [List.flatMap_append,List.flatMap_singleton,List.length_append] at ht
    rw [ht]
    congr 1
    cases p with
    | header lp => rfl
    | receipt rp =>
      have hb : plannedRows lists=pre.flatMap EntityPlan.rows++plannedReceiptRows rp++es.flatMap EntityPlan.rows := by
        rw [←entityPlans_rows,he]
        simp only [List.flatMap_append,List.flatMap_cons,EntityPlan.rows,List.append_assoc]
      have hp : EntityPlan.receipt rp∈entityPlans lists := by rw [he];simp
      apply congrArg some
      exact native_receipt_encoding own ctx lists log constants pub digests fallback headerFallback
        rp _ _ hb (entityPlans_receipt_wf lists hw rp hp)

include hw in
/-- Exact source-list grouping of canonical receipt encodings. Empty lists,
repeated sources, and headers are preserved, not recovered from flattened order. -/
theorem canonical_grouped_encodings (hh : 2^log<Algebra.P)
    (hL : TableLocal ReceiptCandidateRouting.candidateTable
      (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0 0 bs e) :
    (bs.map (fun B=>(B.view (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0).rs.map (fun x=>x.enc)))=
      lists.map (fun xs=>xs.map (fun x=>x.receipt.encode.map UInt8.toNat)) := by
  have he := decoded_native_sequence own ctx lists log constants pub digests fallback headerFallback hw hh
    (ReceiptCandidateProof.repaired_local_base hL) _ e (ListChain.decoded hc)
    (ReceiptCandidateProof.ListChain.end_padding hc).2
  have ht := congrArg (List.map (decodedEncodingToken
    (nativeTrace own ctx lists log constants pub digests fallback headerFallback))) he
  rw [decoded_encoding_tokens] at ht
  have hn := native_entities_encoding own ctx lists log constants pub digests fallback headerFallback hw
    (entityPlans lists) [] rfl
  simp only [List.flatMap_nil,List.length_nil] at hn
  rw [hn,native_encoding_tokens] at ht
  have hg := congrArg decodeGroups ht
  simpa only [decode_group_tokens] using hg

end ZkFormal.NearV3.Assembly.RcptSkeleton
