import ZkFormal.NearV3.Candidates.UniqueSourceNativeBudget
import ZkFormal.NearV3.Rcpt.Candidates.DictionaryCount
namespace ZkFormal.NearV3.Candidates.OriginalSourceReserve
open NearSpec NearSpecV3 ZkFormal.Near Rcpt.Candidates Assembly

/-- Every unused well-shaped dictionary entry pays one 56-byte filler. -/
theorem entry_min (e : ProofEntry) (hk : e.key.length=32) :
    56≤(ZkFormal.V3.encodeEntry e).length := by
  simp only [ZkFormal.V3.encodeEntry,List.length_append,hk,encList,u64,u32,leN,
    List.length_cons,List.length_nil]
  omega

/-- Keep the unused-entry reserve instead of discarding it in a sublist bound. -/
theorem sublist_reserve {α : Type} (f : α→Nat) {xs ys : List α}
    (h : xs.Sublist ys) (hm : ∀y∈ys,56≤f y) :
    (xs.map f).sum+56*ys.length≤(ys.map f).sum+56*xs.length := by
  revert hm
  induction h with
  | slnil => intro _;simp
  | cons a h ih =>
    intro hm
    have ha:=hm a (by simp)
    have ht:=ih (fun y hy=>hm y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega
  | cons_cons a h ih =>
    intro hm
    have ht:=ih (fun y hy=>hm y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

private theorem partition (bs : List SrcpB) :
    (bs.filter fun B=>!B.dup).length+(bs.filter fun B=>B.dup).length=bs.length := by
  induction bs with
  | nil => rfl
  | cons B bs ih => cases hd : B.dup <;> simp [hd] <;> omega

/-- Original source accounting is paid when the native dictionary cardinality
provides an entry for every occurrence, even when computations reuse keys. -/
theorem dictionary_bound (bs : List SrcpB) (computed entries : List ProofEntry)
    (hs : computed.Sublist entries) (hn : bs.length≤entries.length)
    (hk : ∀e∈entries,e.key.length=32)
    (hc : UniqueSourceCharge.size bs=(computed.map fun e=>(ZkFormal.V3.encodeEntry e).length).sum)
    (hl : computed.length=(bs.filter fun B=>!B.dup).length)
    (hd : ∀B∈bs,B.dup=true→B.L=12) :
    DedupRender.size bs+44*bs.length+4≤(encList ZkFormal.V3.encodeEntry entries).length := by
  have hr:=sublist_reserve (fun e : ProofEntry=>(ZkFormal.V3.encodeEntry e).length) hs
    (fun e he=>entry_min e (hk e he))
  have hp:=partition bs
  have he:=UniqueSourceCharge.old_delta bs hd
  simp only [encList,List.length_append,u32_len,concatAll_size]
  rw [←hc,hl] at hr
  omega
end ZkFormal.NearV3.Candidates.OriginalSourceReserve
