import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountLengths

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0 ZkFormal.Near

mutual
theorem native_get_find : ∀(t : PTrie)(key : List Nat),t.get key=(t.find key).join
  | .hash _,_ => rfl
  | .leaf k s m,key => by
    by_cases hk : k=key <;> cases hs : s.get <;> simp [PTrie.get,PTrie.find,hk,hs]
  | .ext k c m,key => by
    simp only [PTrie.get,PTrie.find]
    split <;> simp_all [native_get_find c]
  | .branch v cs m,[] => by
    cases v with
    | none => rfl
    | some s => cases hs : s.get <;> simp [PTrie.get,PTrie.find,hs]
  | .branch v cs m,n::key => native_kids_get_find cs n key
theorem native_kids_get_find : ∀(cs : Kids)(n : Nat)(key : List Nat),
    Kids.get cs n key=(Kids.find cs n key).join
  | .nil,_,_ => rfl
  | .none _,0,_ => rfl
  | .some c _,0,key => native_get_find c key
  | .none cs,n+1,key => native_kids_get_find cs n key
  | .some _ cs,n+1,key => native_kids_get_find cs n key
end

/-- The old value and replacement are both actual 72-byte native accounts. -/
inductive SizedAccountRun : PTrie→List (List Nat×Bytes)→PTrie→Prop
  | nil (t : PTrie) : SizedAccountRun t [] t
  | cons {t mid out : PTrie} {key : List Nat} {old bytes : Bytes} {rest : List (List Nat×Bytes)}
      (read : t.get key=some old) (oldLen : old.length=72) (newLen : bytes.length=old.length)
      (write : t.set key bytes=some mid) (tail : SizedAccountRun mid rest out) :
      SizedAccountRun t ((key,bytes)::rest) out

theorem SizedAccountRun.forget {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : SizedAccountRun pre writes post) : AccountWriteRun pre writes post := by
  induction h with
  | nil t => exact .nil t
  | cons _ _ _ hw _ ih => exact .cons hw ih

theorem native_sized_account_writes (ctx : ApplyCtx) :
    ∀rs i (st out : Acc×List Limit), applyReceipts ctx i st rs=.ok out →
    ∃writes, SizedAccountRun st.1.trie writes out.1.trie ∧
      writes.map Prod.fst=rs.map (fun r => accountKeyPath r.receiverId)
  | [],_,st,out,h => by cases h;exact ⟨[],.nil _,rfl⟩
  | r::rs,i,(acc,ls),out,h => by
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · obtain ⟨acc',ha,h⟩ := bind_ok' h
        obtain ⟨old,bytes,hr,hl,hn,hs⟩ := native_system_write_length ha
        have hg : acc.trie.get (accountKeyPath r.receiverId)=some old := by rw [native_get_find,hr];rfl
        obtain ⟨writes,ht,hk⟩ := native_sized_account_writes ctx rs (i+1) (acc',ls) out h
        exact ⟨(accountKeyPath r.receiverId,bytes)::writes,.cons hg hl hn hs ht,by simp [hk]⟩
      · split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',_,h⟩ := bind_ok' h
          obtain ⟨old,bytes,hr,hl,hn,hs⟩ := native_receipt_write_length ha
          obtain ⟨writes,ht,hk⟩ := native_sized_account_writes ctx rs (i+1) (acc',ls') out h
          exact ⟨(accountKeyPath r.receiverId,bytes)::writes,.cons hr hl hn hs ht,by simp [hk]⟩

private theorem slot_lengths_set : ∀(xs : List (Option Bytes))(i : Nat)(old new : Bytes),
    xs[i]?=some (some old) → new.length=old.length →
    ((xs.set i (some new)).map (Option.map List.length))=xs.map (Option.map List.length)
  | [],_,_,_,h,_ => by simp at h
  | x::xs,0,old,new,h,hl => by
    simp only [List.getElem?_cons_zero,Option.some.injEq] at h
    subst x
    simp [hl]
  | x::xs,i+1,old,new,h,hl => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ,List.map_cons,slot_lengths_set xs i old new h hl]

theorem SizedAccountRun.slot_lengths {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : SizedAccountRun pre writes post) :
    (Prune.vl post).map (Option.map List.length)=(Prune.vl pre).map (Option.map List.length) := by
  induction h with
  | nil t => rfl
  | @cons t mid out key old bytes rest hr _ hn hs _ ih =>
    rw [ih,(Prune.set_same t key bytes mid hs).2.2]
    exact slot_lengths_set _ _ old bytes (Prune.get_vl t key old hr) hn

private theorem compact_lengths (xs : List (Option Bytes)) :
    (xs.filterMap id).map List.length=(xs.map (Option.map List.length)).filterMap id := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [ih]

theorem SizedAccountRun.value_lengths {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : SizedAccountRun pre writes post) :
    (valsOf post).map List.length=(valsOf pre).map List.length := by
  change ((occs post).flatMap ownVals).map List.length=((occs pre).flatMap ownVals).map List.length
  rw [←compact_native_slots,←compact_native_slots,compact_lengths,compact_lengths,h.slot_lengths]

end ZkFormal.NearV3.Rcpt.Candidates
