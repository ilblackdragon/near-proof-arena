import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountIdPermutation
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountPrefixVersion
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

theorem closingAccountViews_total {pre post : PTrie} {keys selected : List (List Nat)} {as : List AcctV}
    (h:closingAccountViews pre post keys selected=some as) (key : List Nat) (hm:key∈selected) :
    ∃a,closingAccountView pre post keys key=some a := by
  induction selected generalizing as with
  | nil=>simp at hm
  | cons k ks ih=>
    cases ha:closingAccountView pre post keys k with
    | none=>simp [closingAccountViews,ha] at h
    | some a=>
      cases ht:closingAccountViews pre post keys ks with
      | none=>simp [closingAccountViews,ha,ht] at h
      | some tail=>
        rcases List.mem_cons.mp hm with rfl|hm
        · exact ⟨a,ha⟩
        · exact ih ht hm

def accountSlot (pre : PTrie) (keys : List (List Nat)) (j : Nat) : Nat :=
  (valueIndex pre (keys.getD j [])).getD 0

theorem nativeAccountViews_keys_defined {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (h:nativeAccountViews pre post rs=some as) :
    ∀key∈rs.map (fun r=>accountKeyPath r.receiverId),∃i,valueIndex pre key=some i := by
  intro key hk
  obtain ⟨a,ha⟩:=closingAccountViews_total h key ((distinctTouched_mem key _).mpr hk)
  exact ⟨a.k,closingAccountView_id ha⟩

theorem accountSlot_key_iff (pre : PTrie) (keys : List (List Nat))
    (ht:∀key∈keys,∃i,valueIndex pre key=some i)
    {key : List Nat} {vid : Nat} (hv:valueIndex pre key=some vid)
    (j : Nat) (hj:j<keys.length) : accountSlot pre keys j=vid ↔ keys[j]=key := by
  obtain ⟨i,hi⟩:=ht keys[j] (List.getElem_mem hj)
  have hg:keys.getD j []=keys[j]:=by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  simp only [accountSlot,hg,hi,Option.getD_some]
  constructor
  · intro he;subst i;exact valueIndex_key_unique pre _ _ vid hi hv
  · intro he;rw [he,hv] at hi;exact (Option.some.inj hi).symm

theorem accountSlot_previous (pre : PTrie) (keys : List (List Nat))
    (ht:∀key∈keys,∃i,valueIndex pre key=some i) (j : Nat) (hj:j<keys.length) :
    closingKeyVersion keys[j] 0 (keys.take j)=NativeMemChain.lb (accountSlot pre keys) (accountSlot pre keys j) j := by
  obtain ⟨i,hi⟩:=ht keys[j] (List.getElem_mem hj)
  have hg:keys.getD j []=keys[j]:=by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  have hs:accountSlot pre keys j=i:=by simp only [accountSlot,hg,hi,Option.getD_some]
  rw [hs]
  exact closingKeyVersion_prefix_lb keys (accountSlot pre keys) _ i
    (accountSlot_key_iff pre keys ht hi) j (by omega)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
