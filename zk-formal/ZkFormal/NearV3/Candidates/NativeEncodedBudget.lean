import ZkFormal.NearV3.Candidates.SizeChargeFields
import ZkFormal.NearV3.Rcpt.Candidates.NativeWitnessCharge
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountPreparedOverhead
namespace ZkFormal.NearV3.Candidates.NativeEncodedBudget
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates HonestStoreRepresentatives

private theorem sum_flatMap {α : Type} (xs : List α) (f : α→List Nat) :
    (xs.flatMap f).sum=(xs.map fun x=>(f x).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem store_charge (bs : List Bytes) :
    (bs.map fun b=>b.length+4).sum=(bs.map List.length).sum+4*bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons,List.sum_cons,List.length_cons];omega

/-- Match actual forest transition stores to native witness transitions; tags
preserve identity but do not add bytes to the serialized store charge. -/
theorem original_charge (ts : List PTrie) (store : Nat→List Bytes) (w : StateWitness)
    (hs : ts.zipIdx.map (fun p=>store p.2)=(transitions w).map Transition.values) :
    charge (NativeStoreRepresentatives.originals ts store)=witnessPayload w+4*witnessRecordCount w := by
  have hh:=congrArg (fun stores : List (List Bytes)=>
    (stores.map fun bs=>(bs.map fun b=>b.length+4).sum).sum) hs
  simp only [List.map_map,Function.comp_def] at hh
  unfold charge NativeStoreRepresentatives.originals
  simp only [List.map_flatMap,sum_flatMap,List.map_map,Function.comp_def]
  rw [hh]
  simp only [store_charge]
  unfold witnessPayload witnessRecordCount transitionPayload transitionRecordCount
  generalize transitions w=trs
  induction trs with
  | nil => rfl
  | cons t trs ih => simp only [List.map_cons,List.sum_cons];omega

/-- The native encoded size limit pays store charge, public fixed overhead,
and actual source bytes. Unused dictionary entries may remain in the witness;
a lower bound on their encoding suffices, without an equality assumption. -/
theorem encoded_budget (ts : List PTrie) (store : Nat→List Bytes) (w : StateWitness)
    (hs : ts.zipIdx.map (fun p=>store p.2)=(transitions w).map Transition.values)
    (he : w.epochId.length=32) (ha : w.appliedReceiptsHash.length=32)
    (ht : ∀t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32)
    (N source : Nat) (pub : List ZkFormal.Algebra.Fp)
    (hd : source+44*N+4≤(encList ZkFormal.V3.encodeEntry w.entries).length)
    (ho : ovhNat pub=224+w.innerBytes.length+44*N+69*w.implicit.length)
    (hb : (ZkFormal.V3.encodeSW w).length≤8388608) :
    ovhNat pub+source+charge (NativeStoreRepresentatives.originals ts store)≤8388608 := by
  have hh:=witness_encoding_charge w he ha ht
  rw [original_charge ts store w hs,ho]
  omega
/-- Candidate public construction supplies the exact natural overhead; callers
need not assume the interpretation of its field encoding. -/
theorem prepared_budget (ts : List PTrie) (store : Nat→List Bytes) (w : StateWitness)
    (hs : ts.zipIdx.map (fun p=>store p.2)=(transitions w).map Transition.values)
    (he : w.epochId.length=32) (ha : w.appliedReceiptsHash.length=32)
    (ht : ∀t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32)
    (p : Prep) (inner bytes : Bytes)
    (hp : SizeCount.countedPreparedBytes p inner=some bytes) (hr : Public.RootsSized p)
    (hi : w.innerBytes=inner) (hk : w.implicit.length=p.hdr.K) (source : Nat)
    (hd : source+44*p.lists.length+4≤(encList ZkFormal.V3.encodeEntry w.entries).length)
    (hb : (ZkFormal.V3.encodeSW w).length≤8388608) :
    ovhNat (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes)+source+
      charge (NativeStoreRepresentatives.originals ts store)≤8388608 := by
  apply encoded_budget ts store w hs he ha ht p.lists.length source _ hd _ hb
  obtain ⟨hbound,rfl⟩:=SizeCount.counted_prepared_bound hp
  rw [Public.prepared_ovhNat p _ hr (by omega)]
  simp [SizeCount.fixedOverhead,hi,hk]

/-- The ordinary indexed native witness store satisfies the alignment premise
when the forest has one tree for each actual transition. -/
theorem store_alignment (ts : List PTrie) (w : StateWitness)
    (hl : ts.length=(transitions w).length) :
    ts.zipIdx.map (fun p=>(((transitions w)[p.2]?).map Transition.values).getD [])=
      (transitions w).map Transition.values := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    have hi : i<(transitions w).length := by simpa using h2
    simp [List.getD,List.getElem?_eq_getElem hi]

end ZkFormal.NearV3.Candidates.NativeEncodedBudget
