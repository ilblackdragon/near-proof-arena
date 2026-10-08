import ZkFormal.NearV3.Candidates.UniqueSourceCharge
import ZkFormal.NearV3.Rcpt.Candidates.NativeSizePartition
namespace ZkFormal.NearV3.Candidates.UniqueSourceDictionarySize
open NearSpec NearSpecV3 ZkFormal.Near Rcpt.Candidates Assembly

private theorem count_partition (bs : List SrcpB) :
    (bs.filter fun B=>!B.dup).length+(bs.filter fun B=>B.dup).length=bs.length := by
  induction bs with
  | nil => rfl
  | cons B bs ih => cases h : B.dup <;> simp [h] <;> omega

theorem selected_count (sources : List SrcList) (bs : List SrcpB)
    (hlen : bs.length=sources.length)
    (hdup : ∀i,i<bs.length→(bs.getD i default).dup=Public.sourceDup sources i) :
    (bs.filter fun B=>!B.dup).length=(firstSourceIndices sources).length := by
  have he : (List.range sources.length).map (fun i=>bs.getD i default)=bs := by
    apply List.ext_getElem (by simp [hlen])
    intro i hi hj
    have hib : i<bs.length := hj
    simp [List.getD,List.getElem?_eq_getElem hib]
  rw [←he,List.filter_map,List.length_map]
  unfold firstSourceIndices
  apply congrArg List.length
  apply List.filter_congr
  intro i hi
  have hh:=List.mem_range.mp hi
  simp only [Function.comp_def,hdup i (by omega)]

theorem computed_charge (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB)
    (hlen : bs.length=sources.length)
    (hdup : ∀i,i<bs.length→(bs.getD i default).dup=Public.sourceDup sources i)
    (hskip : ∀i,i<bs.length→(bs.getD i default).dup=true→(bs.getD i default).L=12)
    (hcost : ∀i,i<sources.length→Public.sourceDup sources i=false→
      entrySizeCharge (nativeEntryAt sources own rs bs i).entry=
        (bs.getD i default).L+33*(bs.getD i default).path.length) :
    UniqueSourceCharge.size bs=
      ((firstNativeEntries sources own rs bs).map entrySizeCharge).sum+
      44*(firstNativeEntries sources own rs bs).length := by
  have hdelta:=UniqueSourceCharge.old_delta bs (by
    intro B hB hd
    obtain ⟨i,hi,hBi⟩:=List.getElem_of_mem hB
    have he : bs.getD i default=B := by simp [List.getD,List.getElem?_eq_getElem hi,hBi]
    simpa only [he] using hskip i hi (by simpa only [he] using hd))
  have hs:=source_size_partition sources bs own rs hlen hdup hskip hcost
  have hn:=selected_count sources bs hlen hdup
  have hc:=count_partition bs
  have he : (firstNativeEntries sources own rs bs).length=(firstSourceIndices sources).length := by
    simp [firstNativeEntries,firstNativeSources]
  rw [he]
  omega

/-- Exact encoding of the actual unique native dictionary, with zero fillers.
Repeated prepared sources still reuse their first authenticated entry. -/
theorem encoded_size (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB)
    (hlen : bs.length=sources.length)
    (hdup : ∀i,i<bs.length→(bs.getD i default).dup=Public.sourceDup sources i)
    (hskip : ∀i,i<bs.length→(bs.getD i default).dup=true→(bs.getD i default).L=12)
    (hcost : ∀i,i<sources.length→Public.sourceDup sources i=false→
      entrySizeCharge (nativeEntryAt sources own rs bs i).entry=
        (bs.getD i default).L+33*(bs.getD i default).path.length)
    (hk : ∀e∈firstNativeEntries sources own rs bs,e.key.length=32)
    (hp : ∀e∈firstNativeEntries sources own rs bs,∀s∈e.proof.path,s.1.length=32) :
    (encList ZkFormal.V3.encodeEntry
      ((nativeDictionary sources own rs bs []).map DictionaryEntryV3.entry)).length=
      UniqueSourceCharge.size bs+4 := by
  rw [nativeDictionary_entries,List.append_nil]
  simp only [encList,List.length_append,u32_len,concatAll_size]
  rw [SourceDictionaryBudget.computed_encoding _ hk hp,computed_charge sources own rs bs hlen hdup hskip hcost]
  omega
end ZkFormal.NearV3.Candidates.UniqueSourceDictionarySize
