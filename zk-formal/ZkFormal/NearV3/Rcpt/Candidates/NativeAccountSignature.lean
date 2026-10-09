import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountStep
import ZkFormal.NearV3.Rcpt.Candidates.NativeSetValues
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

/-- Preserve both account decodability and its immutable suffix. Non-account
values keep their own signature too, so untouched empty values are retained. -/
def accountSignature (b : Bytes) : Bool×Bytes := ((Account.decode b).isSome,b.drop 16)

theorem account_update_signature {pre : Bytes} {a : Account} (hd:Account.decode pre=some a)
    (amount : Nat) (ha:amount<Params.u128Max) :
    accountSignature ({a with amount:=amount}.encode)=accountSignature pre := by
  have hw:=Sound.decode_wf hd
  have hnew:=Sound.decode_encode {a with amount:=amount} ha hw.2.1 hw.2.2.1 hw.2.2.2.1
  simp only [accountSignature,hnew,hd,Option.isSome_some,Prod.mk.injEq,true_and]
  rw [←Sound.encode_decode hd]
  simp [Account.encode,List.append_assoc,List.drop_append,u128,leN_length]

private theorem map_set_preserved {α β : Type} (f : α→β) :
    ∀(xs : List α)(i : Nat)(old new : α), xs[i]?=some old→f new=f old→(xs.set i new).map f=xs.map f
  | [],_,_,_,h,_=>by simp at h
  | x::xs,0,old,new,h,he=>by
    simp only [List.getElem?_cons_zero,Option.some.injEq] at h
    subst old
    simp [he]
  | x::xs,i+1,old,new,h,he=>by
    simpa only [List.set_cons_succ,List.map_cons] using congrArg (List.cons (f x))
      (map_set_preserved f xs i old new h he)

theorem account_write_signatures {st out : TransferV1.Acc} {r : Receipt}
    (h:NativeAccountWrite st out r) :
    (NearSpecV3.valsOf out.trie).map accountSignature=(NearSpecV3.valsOf st.trie).map accountSignature := by
  obtain ⟨raw,a,hr,hd,ha,hs⟩:=h
  obtain ⟨i,hi,hvals,hb⟩:=native_set_values _ _ _ _ hs
  have hf:st.trie.find (accountKeyPath r.receiverId)=some (some raw):=by
    rw [native_get_find] at hr
    cases hh:st.trie.find (accountKeyPath r.receiverId) <;> simp [hh] at hr
    rename_i v
    cases v <;> simp_all
  obtain ⟨j,hj,hread⟩:=valueIndex_complete _ _ _ hf
  have he:i=j:=Option.some.inj (hi.symm.trans hj)
  subst j
  rw [hvals]
  exact map_set_preserved accountSignature _ i raw _ hread (account_update_signature hd _ ha)

/-- Native sequential receipts preserve immutable account bytes at every
compact occurrence, including repeated writes and all untouched values. -/
theorem native_receipt_signatures (ctx : ApplyCtx) :
    ∀rs i (st out : TransferV1.Acc×List Limit),applyReceipts ctx i st rs=.ok out →
      (NearSpecV3.valsOf out.1.trie).map accountSignature=
        (NearSpecV3.valsOf st.1.trie).map accountSignature
  | [],_,st,out,h=>by cases h;rfl
  | r::rs,i,(acc,ls),out,h=>by
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · obtain ⟨acc',ha,h⟩:=Sched.bind_ok h
        exact (native_receipt_signatures ctx rs (i+1) (acc',ls) out h).trans
          (account_write_signatures (system_account_write ha))
      · split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',_,h⟩:=Sched.bind_ok h
          exact (native_receipt_signatures ctx rs (i+1) (acc',ls') out h).trans
            (account_write_signatures (receipt_account_write ha))

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
