import ZkFormal.NearV3.Rcpt.Candidates.NativeForestLookup
import ZkFormal.NearV3.Spec.StoreBuilt

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen

theorem native_account_lookup_rows (wid tau nid vid : Nat) (tree : PTrie)
    (accountId : Bytes) (steps : List WStep3) (ha : accountId.length≤64)
    (h : nativeLookupSteps nid vid tree (accountKeyPath accountId)=some steps) :
    (nativeLookupWalk wid tau nid tree steps).steps.length≤132 := by
  rw [nativeLookupWalk_length wid tau nid vid tree (accountKeyPath accountId) steps h]
  simp only [accountKeyPath,nibbles_length,List.length_cons]
  omega

theorem native_forest_account_lookup_wf (before after : List PTrie) (tree : PTrie) (wid : Nat)
    (accountId : Bytes) (steps : List WStep3) (hw : tree.wf=true)
    (hb : Assembly.preBytes (before++tree::after)≤2000000)
    (hts : (before++tree::after).length≤P) (hwid : wid<P) (ha : accountId.length≤64)
    (h : nativeLookupSteps (forestLookupNid before) (forestLookupVid before) tree
      (accountKeyPath accountId)=some steps) :
    WalkWf3 [nativeLookupWalk wid before.length (forestLookupNid before) tree steps] := by
  apply native_forest_lookup_wf before after tree wid _ steps hw hb hts hwid ?_ ?_ h
  · have hk:=nibbles_ok (0::accountId)
    simpa [accountKeyPath,nibblesOk,List.all_eq_true] using hk
  · simp only [accountKeyPath,nibbles_length,List.length_cons]
    omega

/-- Every successful native account lookup constructs a locally valid bounded walk. -/
theorem native_account_lookup_complete (before after : List PTrie) (tree : PTrie) (wid : Nat)
    (accountId : Bytes) (value : Option Bytes) (hw : tree.wf=true)
    (hb : Assembly.preBytes (before++tree::after)≤2000000)
    (hts : (before++tree::after).length≤P) (hwid : wid<P) (ha : accountId.length≤64)
    (hfind : tree.find (accountKeyPath accountId)=some value) :
    ∃steps,nativeLookupSteps (forestLookupNid before) (forestLookupVid before) tree
      (accountKeyPath accountId)=some steps ∧
      WalkWf3 [nativeLookupWalk wid before.length (forestLookupNid before) tree steps] ∧
      (nativeLookupWalk wid before.length (forestLookupNid before) tree steps).steps.length≤132 := by
  have hd:=nativeLookupSteps_defined (forestLookupNid before) (forestLookupVid before) tree
    (accountKeyPath accountId)
  rw [hfind] at hd
  cases h : nativeLookupSteps (forestLookupNid before) (forestLookupVid before) tree
      (accountKeyPath accountId) with
  | none=>simp [h] at hd
  | some steps=>
    exact ⟨steps,rfl,native_forest_account_lookup_wf before after tree wid accountId steps hw hb hts hwid ha h,
      native_account_lookup_rows wid before.length _ _ tree accountId steps ha h⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
