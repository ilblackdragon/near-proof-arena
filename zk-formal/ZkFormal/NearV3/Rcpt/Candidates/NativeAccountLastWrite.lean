import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountMemoryVersion
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedScheduler
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

/-- The final concrete native write and its receipt version; repeated keys
replace the same record without losing their full global position. -/
def lastWriteRecord (key : List Nat) : Nat→List (List Nat×Bytes)→Option (Nat×Bytes)
  | _,[]=>none
  | start,(k,b)::rest=>match lastWriteRecord key (start+1) rest with
    | some r=>some r
    | none=>if k=key then some (start+1,b) else none

theorem lastWriteRecord_none (key : List Nat) (start : Nat) (ws : List (List Nat×Bytes)) :
    lastWriteRecord key start ws=none ↔ key∉ws.map Prod.fst := by
  induction ws generalizing start with
  | nil=>simp [lastWriteRecord]
  | cons w ws ih=>
    cases hl:lastWriteRecord key (start+1) ws with
    | none=>have hn:=(ih (start+1)).mp hl;simp [lastWriteRecord,hl,hn,eq_comm]
    | some p=>
      have hm:key∈ws.map Prod.fst:=by
        by_cases hm:key∈ws.map Prod.fst
        · exact hm
        · have he:=(ih (start+1)).mpr hm
          simp [hl] at he
      simp [lastWriteRecord,hl,hm]

theorem lastWriteRecord_version (key : List Nat) (start : Nat) (ws : List (List Nat×Bytes)) :
    ((lastWriteRecord key start ws).map Prod.fst).getD 0=
      closingKeyVersion key start (ws.map Prod.fst) := by
  induction ws generalizing start with
  | nil=>rfl
  | cons w ws ih=>
    cases hl:lastWriteRecord key (start+1) ws with
    | none=>
      have hz:closingKeyVersion key (start+1) (ws.map Prod.fst)=0:=by simpa [hl] using (ih (start+1)).symm
      by_cases hk:w.1=key <;> simp [lastWriteRecord,hl,closingKeyVersion,hz,hk]
    | some p=>
      have hm:key∈ws.map Prod.fst:=by
        by_cases hm:key∈ws.map Prod.fst
        · exact hm
        · have he:=(lastWriteRecord_none key (start+1) ws).mpr hm
          simp [hl] at he
      have hz:closingKeyVersion key (start+1) (ws.map Prod.fst)≠0:=fun h=>(closingKeyVersion_zero _ _ _).mp h hm
      simpa [lastWriteRecord,hl,closingKeyVersion,hz] using ih (start+1)

/-- Final native lookup is exactly the last written payload, or its original
payload when the key is untouched. This uses real sequential set execution. -/
theorem AccountWriteRun.last_read {pre post : PTrie} {ws : List (List Nat×Bytes)}
    (hr:AccountWriteRun pre ws post) (key : List Nat) (start : Nat) :
    post.find key=match lastWriteRecord key start ws with
      | none=>pre.find key
      | some r=>some (some r.2) := by
  induction hr generalizing start with
  | nil=>rfl
  | @cons pre mid post k b rest hs ht ih=>
    rw [ih (start+1)]
    cases hl:lastWriteRecord key (start+1) rest with
    | some p=>simp [lastWriteRecord,hl]
    | none=>
      by_cases he:k=key
      · subst k
        simpa [lastWriteRecord,hl] using ZkFormal.NearV3.PTrie.find_set_self _ _ _ _ hs
      · simpa [lastWriteRecord,hl,he] using ZkFormal.NearV3.PTrie.find_set_ne _ _ _ _ _ hs (Ne.symm he)

theorem closingAccountView_last_write {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (hr:AccountWriteRun pre writes post) {keys : List (List Nat)}
    (hkeys:writes.map Prod.fst=keys) {key : List Nat} (hm:key∈keys)
    {a : AcctV} (ha:closingAccountView pre post keys key=some a) :
    ∃bytes,lastWriteRecord key 0 writes=some (a.tlast,bytes) ∧ post.find key=some (some bytes) := by
  cases hl:lastWriteRecord key 0 writes with
  | none=>
    have hn:=(lastWriteRecord_none key 0 writes).mp hl
    exact False.elim (hn (hkeys ▸ hm))
  | some p=>
    have hv:=lastWriteRecord_version key 0 writes
    simp only [hl,Option.map_some,Option.getD_some,hkeys] at hv
    have ht:p.1=a.tlast:=hv.trans (closingAccountView_version ha).symm
    refine ⟨p.2,?_,?_⟩
    · simpa only [←ht] using hl
    · simpa only [hl] using AccountWriteRun.last_read hr key 0

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
