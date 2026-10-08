import ZkFormal.NearV3.Rcpt.Candidates.NativeSetInputValue
import ZkFormal.NearV3.Rcpt.Candidates.NativeWriteSkeleton

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec

/-- Replay exactly the same ordered writes on another trie whose affected reads
agree. Repeated writes are retained; no structural scheduler equality is used. -/
theorem AccountWriteRun.rebase {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : AccountWriteRun pre writes post) (querySet : List Nat→Prop)
    (hkeys : ∀key∈writes.map Prod.fst,querySet key) (other : PTrie)
    (hread : ∀key,querySet key→other.find key=pre.find key) :
    ∃final,AccountWriteRun other writes final ∧
      ∀key,querySet key→final.find key=post.find key := by
  induction h generalizing other with
  | nil pre=>exact ⟨other,.nil other,hread⟩
  | @cons pre mid post key value rest hs ht ih=>
    obtain ⟨old,hold⟩:=native_set_input_value pre key value mid hs
    have hkey:=hkeys key (by simp)
    obtain ⟨otherMid,hset⟩:=native_set_exists other key old value (by rw [hread key hkey];exact hold)
    have hmid : ∀q,querySet q→otherMid.find q=mid.find q := by
      intro q hq
      by_cases he:q=key
      · subst q
        rw [ZkFormal.NearV3.PTrie.find_set_self _ _ _ _ hset,
          ZkFormal.NearV3.PTrie.find_set_self _ _ _ _ hs]
      · rw [ZkFormal.NearV3.PTrie.find_set_ne _ _ _ _ _ hset he,
          ZkFormal.NearV3.PTrie.find_set_ne _ _ _ _ _ hs he]
        exact hread q hq
    obtain ⟨final,hfinal,heq⟩:=ih (fun q hq=>hkeys q (by simp [hq])) otherMid hmid
    exact ⟨final,.cons hset hfinal,heq⟩

/-- The rebased old tree changes only revealed slot bytes and retains its
original node allocation, even if the scheduler intermediate has another shape. -/
theorem AccountWriteRun.rebase_skeleton {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : AccountWriteRun pre writes post) (querySet : List Nat→Prop)
    (hkeys : ∀key∈writes.map Prod.fst,querySet key) (other : PTrie)
    (hread : ∀key,querySet key→other.find key=pre.find key) :
    ∃final,AccountWriteRun other writes final ∧ WriteTreePair other final ∧
      ∀key,querySet key→final.find key=post.find key := by
  obtain ⟨final,hf,he⟩:=AccountWriteRun.rebase h querySet hkeys other hread
  exact ⟨final,hf,hf.skeleton,he⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
