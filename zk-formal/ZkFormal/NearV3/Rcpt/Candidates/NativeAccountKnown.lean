import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountTouches
import ZkFormal.NearV3.Assembly.SetRevealed
import ZkFormal.NearV3.Rcpt.Candidates.NativeQueueLookupRows

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0 Assembly

/-- A set never creates a previously unresolved path, even at the updated key. -/
theorem set_known_reverse {pre post : PTrie} {key query : List Nat} {value : Bytes}
    (hs : pre.set key value=some post) (hk : post.find query≠none) : pre.find query≠none := by
  by_cases he : key=query
  · subst query
    exact set_input_known _ _ _ _ hs
  · rw [ZkFormal.NearV3.PTrie.find_set_ne _ _ _ _ _ hs (Ne.symm he)] at hk
    exact hk

/-- All touched accounts were already readable before the receipt stage;
repeated writes do not justify an extra prestate assumption. -/
theorem AccountWriteRun.input_known {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : AccountWriteRun pre writes post) : ∀key∈writes.map Prod.fst,pre.find key≠none := by
  induction h with
  | nil t=>simp
  | @cons t mid out key bytes rest hs ht ih=>
    intro query hq
    simp only [List.map_cons,List.mem_cons] at hq
    rcases hq with rfl|hq
    · exact set_input_known _ _ _ _ hs
    · exact set_known_reverse hs (ih query hq)

theorem native_accounts_input_known {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : Acc×List Limit} (h : applyReceipts ctx i st rs=.ok out) :
    ∀r∈rs,st.1.trie.find (accountKeyPath r.receiverId)≠none := by
  obtain ⟨writes,hr,hkeys⟩:=native_account_writes ctx rs i st out h
  intro r hrmem
  apply AccountWriteRun.input_known hr
  rw [hkeys]
  exact List.mem_map.mpr ⟨r,hrmem,rfl⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
