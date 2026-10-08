import ZkFormal.NearV3.Rcpt.Candidates.NativeSetValues

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec Assembly

theorem writtenValueIds_same {pre post : PTrie} (h : WriteTreePair pre post)
    (writes : List (List Nat×Bytes)) : writtenValueIds pre writes=writtenValueIds post writes := by
  unfold writtenValueIds
  congr 1
  funext w
  exact write_value_index h w.1

/-- Values outside the actual write set remain byte-for-byte unchanged, at
exact compact occurrence IDs, even when earlier writes repeat other IDs. -/
theorem AccountWriteRun.untouched {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : AccountWriteRun pre writes post) (i : Nat) (hn : i∉writtenValueIds pre writes) :
    (NearSpecV3.valsOf post)[i]?=(NearSpecV3.valsOf pre)[i]? := by
  induction h with
  | nil=>rfl
  | @cons pre mid post key value rest hs ht ih=>
    obtain ⟨j,hj,hvals,hbound⟩:=native_set_values pre key value mid hs
    have hne : i≠j := by
      intro he
      apply hn
      simp [writtenValueIds,hj,he]
    have hrest : i∉writtenValueIds mid rest := by
      rw [←writtenValueIds_same (native_set_pair _ _ _ _ hs)]
      intro hi
      apply hn
      simp only [writtenValueIds,List.filterMap_cons,hj]
      exact List.mem_cons_of_mem j hi
    rw [ih hrest,hvals]
    simp [Ne.symm hne]

/-- The touched-only concrete constructor really may retain original digests
for every inactive value: replay supplied equality of the actual bytes. -/
theorem oldTreeInputs_inactive_bytes {pre oldPost : PTrie} {writes : List (List Nat×Bytes)}
    (h : AccountWriteRun pre writes oldPost) (i : Nat) (hn : i∉writtenValueIds pre writes) :
    (oldTreeInputs pre oldPost writes).value i=none ∧
      (NearSpecV3.valsOf oldPost)[i]?=(NearSpecV3.valsOf pre)[i]? :=
  ⟨oldTreeInputs_unwritten _ _ _ i hn,AccountWriteRun.untouched h i hn⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
