import ZkFormal.NearV3.Candidates.NativeReceiptAccessIds

namespace ZkFormal.NearV3.Candidates.NativeAccessByteOwnership
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem keys_disjoint (account receiver : Bytes) (pk : PublicKey) :
    accountKeyPath account≠keyAccessKey receiver pk := by
  simp [accountKeyPath,keyAccessKey,nibbles]

/-- Account and access-key byte providers cannot claim the same original VID. -/
theorem slots_disjoint {pre : PTrie} {account receiver : Bytes} {pk : PublicKey}
    {i j : Nat} (ha:valueIndex pre (accountKeyPath account)=some i)
    (hk:valueIndex pre (keyAccessKey receiver pk)=some j) : i≠j := by
  intro he
  subst j
  exact keys_disjoint account receiver pk (valueIndex_key_unique pre _ _ i ha hk)

/-- Every existing access-key slot lies in the explicit non-account portion
of the original forest byte inventory; repeated access queries do not allocate
additional value records. -/
theorem outside_account_writes {pre : PTrie} {rs : List Receipt}
    {writes : List (List Nat×Bytes)}
    (hw:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    {receiver : Bytes} {pk : PublicKey} {i : Nat}
    (hi:valueIndex pre (keyAccessKey receiver pk)=some i) :
    i∉writtenValueIds pre writes := by
  intro hm
  obtain ⟨key,hkey,hslot⟩:=List.mem_filterMap.mp hm
  have hmapped:key.1∈writes.map Prod.fst:=List.mem_map.mpr ⟨key,hkey,rfl⟩
  rw [hw] at hmapped
  obtain ⟨r,hr,he⟩:=List.mem_map.mp hmapped
  rw [←he] at hslot
  exact slots_disjoint hslot hi rfl

theorem remaining_slot {pre : PTrie} {rs : List Receipt}
    {writes : List (List Nat×Bytes)}
    (hw:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    {receiver : Bytes} {pk : PublicKey} {i : Nat}
    (hi:valueIndex pre (keyAccessKey receiver pk)=some i) :
    i∈(List.range (NearSpecV3.valsOf pre).length).filter
      (fun j=>!(decide (j∈writtenValueIds pre writes))) := by
  obtain ⟨bytes,_,hb⟩:=NativeReceiptAccessIds.bytes_at hi
  obtain ⟨hlt,_⟩:=List.getElem?_eq_some_iff.mp hb
  have hn:=outside_account_writes hw hi
  simp [List.mem_filter,List.mem_range,hlt,hn]

end ZkFormal.NearV3.Candidates.NativeAccessByteOwnership
