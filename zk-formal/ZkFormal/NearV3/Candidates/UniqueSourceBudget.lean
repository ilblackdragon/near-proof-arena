import ZkFormal.NearV3.Candidates.UniqueSourceCharge
namespace ZkFormal.NearV3.Candidates.UniqueSourceBudget
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates

def overhead (p : Prep) (inner : Bytes) : Nat := 224+inner.length+69*p.hdr.K

def preparedBytes (p : Prep) (inner : Bytes) : Option Bytes :=
  if overhead p inner≤8388608 then some (Public.preparedBytes p (overhead p inner)) else none

theorem dictionary_bound (bs : List SrcpB) (computed entries : List ProofEntry)
    (hs : computed.Sublist entries)
    (hk : ∀e∈computed,e.key.length=32)
    (hp : ∀e∈computed,∀s∈e.proof.path,s.1.length=32)
    (hc : ((bs.filter fun B=>!B.dup).map fun B=>B.L+33*B.path.length)=computed.map entrySizeCharge) :
    UniqueSourceCharge.size bs+4≤(encList ZkFormal.V3.encodeEntry entries).length := by
  have hh:=SourceDictionaryBudget.selected_dictionary_le computed entries hs hk hp
  have hn:=congrArg List.length hc
  simp only [List.length_map] at hn
  rw [UniqueSourceCharge.computed_sum,hc,hn]
  exact hh

/-- Existing native encoded size admission guarantees the corrected public
constructor succeeds; there is no per-occurrence filler admission penalty. -/
theorem public_complete (p : Prep) (inner : Bytes) (w : StateWitness)
    (he : w.epochId.length=32) (ha : w.appliedReceiptsHash.length=32)
    (ht : ∀t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32)
    (hi : w.innerBytes=inner) (hk : w.implicit.length=p.hdr.K)
    (hb : (ZkFormal.V3.encodeSW w).length≤8388608) :
    preparedBytes p inner=some (Public.preparedBytes p (overhead p inner)) := by
  have hh:=witness_encoding_charge w he ha ht
  have hd : 4≤(encList ZkFormal.V3.encodeEntry w.entries).length := by
    simp only [encList,List.length_append,u32_len];omega
  have ho : overhead p inner≤8388608 := by unfold overhead; rw [hi,hk] at hh;omega
  simp [preparedBytes,ho]

theorem public_bound (p : Prep) (inner bytes : Bytes) (h : preparedBytes p inner=some bytes) :
    overhead p inner≤8388608 ∧ bytes=Public.preparedBytes p (overhead p inner) := by
  unfold preparedBytes at h
  split at h
  · exact ⟨by assumption,(Option.some.inj h).symm⟩
  · cases h

theorem public_overhead (p : Prep) (inner bytes : Bytes) (h : preparedBytes p inner=some bytes)
    (hr : Public.RootsSized p) : ovhNat (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes)=overhead p inner := by
  obtain ⟨hb,rfl⟩:=public_bound p inner bytes h
  exact Public.prepared_ovhNat p _ hr (by omega)

/-- Corrected source charge plus original stores fits the native byte cap.
Source-to-selected-entry binding and native store alignment remain explicit. -/
theorem encoded_budget (ts : List PTrie) (store : Nat→List Bytes) (w : StateWitness)
    (hs : ts.zipIdx.map (fun p=>store p.2)=(transitions w).map Transition.values)
    (he : w.epochId.length=32) (ha : w.appliedReceiptsHash.length=32)
    (ht : ∀t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32)
    (p : Prep) (inner bytes : Bytes) (hpub : preparedBytes p inner=some bytes)
    (hr : Public.RootsSized p) (hi : w.innerBytes=inner) (hk : w.implicit.length=p.hdr.K)
    (bs : List SrcpB)
    (hd : UniqueSourceCharge.size bs+4≤(encList ZkFormal.V3.encodeEntry w.entries).length)
    (hb : (ZkFormal.V3.encodeSW w).length≤8388608) :
    ovhNat (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes)+UniqueSourceCharge.size bs+
      HonestStoreRepresentatives.charge (NativeStoreRepresentatives.originals ts store)≤8388608 := by
  have hh:=witness_encoding_charge w he ha ht
  rw [public_overhead p inner bytes hpub hr,NativeEncodedBudget.original_charge ts store w hs]
  unfold overhead
  rw [hi,hk] at hh
  omega
end ZkFormal.NearV3.Candidates.UniqueSourceBudget
