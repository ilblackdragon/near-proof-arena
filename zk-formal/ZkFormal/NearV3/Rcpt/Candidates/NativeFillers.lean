import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionaryCount
import ZkFormal.NearV3.Rcpt.Candidates.PreparedSourceCount
import ZkFormal.NearV3.Spec.Codec
import ZkFormal.V3.EncodeWitness

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

/-- A 32-byte key enumeration; no hash-preimage or collision assumption is used. -/
def fillerKeys (n : Nat) : List Bytes := (List.range n).map (leN 32)

theorem fillerKeys_nodup {n : Nat} (hn : n≤3968) : (fillerKeys n).Nodup := by
  apply List.pairwise_map.mpr
  apply List.pairwise_lt_range.imp_of_mem
  intro i j hi hj hij he
  have hi' : i<256^32 := by have := List.mem_range.mp hi; omega
  have hj' : j<256^32 := by have := List.mem_range.mp hj; omega
  have hh := congrArg leNat he
  rw [leNat_leN' 32 i hi',leNat_leN' 32 j hj'] at hh
  omega

private theorem filters_length {α : Type} (p : α → Bool) (xs : List α) :
    (xs.filter p).length+(xs.filter fun x => !p x).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h] <;> omega

/-- At most one candidate is excluded per prepared occurrence. Twice the actual
source count provides enough fresh keys even if all source keys hit this enumeration. -/
theorem freshKeys_capacity (sources : List SrcList) (hn : sources.length≤1984) :
    sources.length≤((fillerKeys (2*sources.length)).filter
      (fun key => !(sources.map SrcList.key).contains key)).length := by
  have hd := fillerKeys_nodup (n := 2*sources.length) (by omega)
  have hs : ((fillerKeys (2*sources.length)).filter
      (fun key => (sources.map SrcList.key).contains key)).length≤sources.length := by
    have hh := List.Nodup.length_le_of_subset (hd.filter (fun key => (sources.map SrcList.key).contains key))
      (l₂ := sources.map SrcList.key) (by intro key hk; simpa using (List.mem_filter.mp hk).2)
    simpa only [List.length_map] using hh
  have hh := filters_length (fun key => (sources.map SrcList.key).contains key) (fillerKeys (2*sources.length))
  have hl : (fillerKeys (2*sources.length)).length=2*sources.length := by simp [fillerKeys]
  rw [hl] at hh
  omega

/-- Unused native entries use bounded zero shard IDs and empty receipt/path vectors. -/
def fillerEntry (key : Bytes) : ProofEntry := ⟨key,[],⟨0,0,[]⟩⟩

def nativeFillers (sources : List SrcList) : List ProofEntry :=
  (((fillerKeys (2*sources.length)).filter (fun key => !(sources.map SrcList.key).contains key)).take
    (sources.length-(firstSourceIndices sources).length)).map fillerEntry

theorem nativeFillers_length (sources : List SrcList) (hn : sources.length≤1984) :
    (nativeFillers sources).length=sources.length-(firstSourceIndices sources).length := by
  have hh := freshKeys_capacity sources hn
  simp only [nativeFillers,List.length_map,List.length_take]
  omega

theorem nativeFillers_nodup (sources : List SrcList) (hn : sources.length≤1984) :
    ((nativeFillers sources).map ProofEntry.key).Nodup := by
  simpa only [List.Nodup,nativeFillers,List.map_map,Function.comp_def,fillerEntry,List.map_id'] using
    ((fillerKeys_nodup (n := 2*sources.length) (by omega)).filter
      (fun key => !(sources.map SrcList.key).contains key)).take (i := sources.length-(firstSourceIndices sources).length)

theorem nativeFillers_fresh (sources : List SrcList) :
    ∀ f∈nativeFillers sources,∀ s∈sources,f.key≠s.key := by
  intro f hf s hs he
  obtain ⟨key,hk,rfl⟩ := List.mem_map.mp hf
  have ht := List.mem_of_mem_take hk
  have hh := (List.mem_filter.mp ht).2
  have hm : key∈sources.map SrcList.key := List.mem_map.mpr ⟨s,hs,he.symm⟩
  simp [hm] at hh

theorem nativeFillers_key_length (sources : List SrcList) {f : ProofEntry}
    (hf : f∈nativeFillers sources) : f.key.length=32 := by
  obtain ⟨key,hk,rfl⟩ := List.mem_map.mp hf
  have ht := (List.mem_filter.mp (List.mem_of_mem_take hk)).1
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
  exact leN_len 32 i

theorem nativeFillers_entry_size (sources : List SrcList) {f : ProofEntry}
    (hf : f∈nativeFillers sources) : (V3.encodeEntry f).length=56 := by
  have hl := nativeFillers_key_length sources hf
  obtain ⟨key,hk,rfl⟩ := List.mem_map.mp hf
  simp only [fillerEntry] at hl
  simp [V3.encodeEntry,fillerEntry,encList,concatAll,hl]

/-- Filler cardinality is now constructive, with no assumption that source keys
are distinct and no fresh-key oracle. -/
theorem nativeFillers_dictionary_count (sources : List SrcList) (hn : sources.length≤1984)
    (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB) :
    (distinctKeys ((nativeDictionary sources own rs bs (nativeFillers sources)).map Assembly.DictionaryEntryV3.entry)).length=
      sources.length :=
  nativeDictionary_occurrence_count sources own rs bs (nativeFillers sources)
    (nativeFillers_fresh sources) (nativeFillers_nodup sources hn) (nativeFillers_length sources hn)

theorem nativeFillers_entry_wf (sources : List SrcList) {f : ProofEntry}
    (hf : f∈nativeFillers sources) : V3.entryWf f=true := by
  have hl := nativeFillers_key_length sources hf
  obtain ⟨key,hk,rfl⟩ := List.mem_map.mp hf
  simp only [fillerEntry] at hl
  simp [V3.entryWf,V3.h32,fillerEntry,hl]

theorem nativeFillers_decode (sources : List SrcList) {f : ProofEntry}
    (hf : f∈nativeFillers sources) (rest : Bytes) :
    pEntry (V3.encodeEntry f++rest)=.ok (f,rest) :=
  V3.pEntry_encode f (nativeFillers_entry_wf sources hf) rest

theorem nativeFillers_encoded_cost (sources : List SrcList) (hn : sources.length≤1984) :
    ((nativeFillers sources).map (fun f => (V3.encodeEntry f).length)).sum=
      56*(sources.length-(firstSourceIndices sources).length) := by
  have hm : (nativeFillers sources).map (fun f => (V3.encodeEntry f).length)=
      (nativeFillers sources).map (fun _ => 56) := by
    apply List.map_congr_left
    exact fun f hf => nativeFillers_entry_size sources hf
  rw [hm,List.map_const',List.sum_replicate_nat,nativeFillers_length sources hn,Nat.mul_comm]

theorem nativeFillers_cost_bound (sources : List SrcList) (hn : sources.length≤1984) :
    ((nativeFillers sources).map (fun f => (V3.encodeEntry f).length)).sum≤111104 := by
  rw [nativeFillers_encoded_cost sources hn]
  omega

end ZkFormal.NearV3.Rcpt.Candidates
