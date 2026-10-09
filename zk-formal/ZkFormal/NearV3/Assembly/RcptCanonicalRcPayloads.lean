import ZkFormal.NearV3.Assembly.RcptNativeRcHeaders

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

private theorem flatten_map_eq {α β : Type} (xs : List α) (f : α→List β) :
    (xs.map f).flatten=xs.flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.flatten_cons,List.flatMap_cons,ih]

private theorem concat_bytes_map (xs : List Bytes) :
    (concatAll xs).map UInt8.toNat=xs.flatMap (List.map UInt8.toNat) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [concatAll,List.flatMap_cons,List.map_append,ih]

def encodedRcPayload (own : Nat) (encs : List (List Nat)) : List Nat :=
  (u64 own++u32 encs.length).map UInt8.toNat++encs.flatten

theorem encodedRcPayload_native (own : Nat) (xs : List Input) :
    encodedRcPayload own (xs.map (fun x=>x.receipt.encode.map UInt8.toNat))=
      (u64 own++encodeReceipts (xs.map Input.receipt)).map UInt8.toNat := by
  simp only [encodedRcPayload,List.length_map,flatten_map_eq,encodeReceipts,List.map_append,
    List.map_map,concat_bytes_map,List.flatMap_map,Function.comp_def,List.append_assoc]

/-- Complete honest RC SHA preimages, one per actual source occurrence. This
includes exact shard/count headers and preserves empty lists and repetitions. -/
theorem canonical_rc_payloads (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hown : ∀i,i<8→pub.getD (PH_OWN+i) 0=Fp.ofNat (((u64 own).getD i 0).toNat))
    (hL : TableLocal ReceiptCandidateRouting.candidateTable (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 0 bs e) :
    (bs.map (fun B=>let L:=B.view (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0
      hdrBytes pub L++L.rs.flatMap (fun x=>x.enc)))=
      lists.map (fun xs=>(u64 own++encodeReceipts (xs.map Input.receipt)).map UInt8.toNat) := by
  let tr := RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0
  have hg := canonical_grouped_encodings own ctx lists log constants pub digests fallback headerFallback hw hh hL bs e hc
  have he : bs.map (fun B=>hdrBytes pub (B.view tr 0)++(B.view tr 0).rs.flatMap (fun x=>x.enc))=
      (bs.map (fun B=>(B.view tr 0).rs.map (fun x=>x.enc))).map (encodedRcPayload own) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro B hB
    rw [native_rc_header own ctx lists log constants pub digests fallback headerFallback hown
      (ReceiptCandidateProof.repaired_local_base hL) B (ReceiptCandidateProof.ListChain.blocks hc B hB)]
    simp only [encodedRcPayload,List.length_map,flatten_map_eq,Function.comp_def]
    rfl
  change bs.map (fun B=>hdrBytes pub (B.view tr 0)++(B.view tr 0).rs.flatMap (fun x=>x.enc))=_
  rw [he,hg,List.map_map]
  apply List.map_congr_left
  intro xs hxs
  exact encodedRcPayload_native own xs

end ZkFormal.NearV3.Assembly.RcptSkeleton
