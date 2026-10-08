import ZkFormal.NearV3.Rcpt.Candidates.NativeSetWf

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec

/-- Same-length receipt writes commute through the structural scheduler upsert.
The result is exact tree equality, rather than only agreement of lookups. -/
theorem SizedAccountRun.upsert_commute {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : SizedAccountRun pre writes post) (hw : pre.wf=true) (key : List Nat) (value : Bytes)
    (hd : ∀q∈writes.map Prod.fst,q≠key) (sched : PTrie) (hu : pre.upsert key value=some sched) :
    ∃final,post.upsert key value=some final ∧ AccountWriteRun sched writes final := by
  induction h generalizing sched with
  | nil t=>exact ⟨sched,hu,.nil sched⟩
  | @cons pre mid post q old bytes rest hr hl hn hs ht ih=>
    have hq:=hd q (by simp)
    have hlength : ∀b,pre.find q=some (some b)→b.length=bytes.length := by
      intro b hb
      have hh:=hr
      rw [native_get_find,hb] at hh
      have he : b=old := Option.some.inj hh
      rw [he]
      exact hn.symm
    obtain ⟨midSched,hmup,hmset⟩:=ZkFormal.NearV3.PTrie.set_upsert_comm pre q key bytes value mid sched
      hw hq hlength hs hu
    obtain ⟨final,hf,hrun⟩:=ih (native_set_wf _ _ _ _ hs hw (by omega))
      (fun q hq=>hd q (by simp [hq])) midSched hmup
    exact ⟨final,hf,.cons hmset hrun⟩

theorem AccountWriteRun.deterministic {pre a b : PTrie} {writes : List (List Nat×Bytes)}
    (ha : AccountWriteRun pre writes a) (hb : AccountWriteRun pre writes b) : a=b := by
  induction ha with
  | nil t=>cases hb;rfl
  | cons hs ht ih=>
    cases hb with
    | cons hs' ht'=>
      have he:=Option.some.inj (hs.symm.trans hs')
      subst he
      exact ih ht'

/-- Identify the reassembled tree with the actual scheduler-first execution. -/
theorem SizedAccountRun.upsert_actual {pre oldPost sched final : PTrie}
    {writes : List (List Nat×Bytes)} (h : SizedAccountRun pre writes oldPost)
    (hw : pre.wf=true) (key : List Nat) (value : Bytes)
    (hd : ∀q∈writes.map Prod.fst,q≠key) (hu : pre.upsert key value=some sched)
    (actual : AccountWriteRun sched writes final) : oldPost.upsert key value=some final := by
  obtain ⟨out,hout,hrun⟩:=SizedAccountRun.upsert_commute h hw key value hd sched hu
  rw [AccountWriteRun.deterministic hrun actual] at hout
  exact hout

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
