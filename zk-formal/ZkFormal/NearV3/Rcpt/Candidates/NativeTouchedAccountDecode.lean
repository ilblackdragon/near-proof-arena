import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountPair
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

def AccountAt (t : PTrie) (key : List Nat) : Prop :=
  ∃i bs a,valueIndex t key=some i ∧ (NearSpecV3.valsOf t)[i]?=some bs ∧ Account.decode bs=some a

theorem written_account_at {st out : TransferV1.Acc} {r : Receipt}
    (h:NativeAccountWrite st out r) : AccountAt st.trie (accountKeyPath r.receiverId) := by
  obtain ⟨raw,a,hr,hd,_,_⟩:=h
  have hf:st.trie.find (accountKeyPath r.receiverId)=some (some raw):=by
    rw [native_get_find] at hr
    cases hh:st.trie.find (accountKeyPath r.receiverId) <;> simp [hh] at hr
    rename_i v
    cases v <;> simp_all
  obtain ⟨i,hi,hv⟩:=valueIndex_complete _ _ _ hf
  exact ⟨i,raw,a,hi,hv,hd⟩

theorem accountAt_back {pre post : PTrie} {key : List Nat}
    (hp:WriteTreePair pre post)
    (he:(NearSpecV3.valsOf post).map accountSignature=(NearSpecV3.valsOf pre).map accountSignature)
    (ha:AccountAt post key) : AccountAt pre key := by
  obtain ⟨i,after,a,hi,hv,hd⟩:=ha
  have hx:=congrArg (fun xs=>xs[i]?) he
  simp only [List.getElem?_map,hv,Option.map_some] at hx
  cases hb:(NearSpecV3.valsOf pre)[i]? with
  | none=>simp [hb] at hx
  | some before=>
    simp only [hb,Option.map_some,Option.some.injEq] at hx
    obtain ⟨b,hbdec,_⟩:=signature_decoded_before hx hd
    exact ⟨i,before,b,(write_value_index hp key).trans hi,hb,hbdec⟩

theorem account_write_back {st out : TransferV1.Acc} {r : Receipt} {key : List Nat}
    (h:NativeAccountWrite st out r) (ha:AccountAt out.trie key) : AccountAt st.trie key := by
  have he:=account_write_signatures h
  obtain ⟨raw,a,_,_,_,hs⟩:=h
  exact accountAt_back (native_set_pair _ _ _ _ hs) he ha

/-- Every touched receiver is already a decodable account in the INITIAL
receipt-stage trie, including receivers first touched after other writes. -/
theorem native_touched_account_decode (ctx : ApplyCtx) :
    ∀rs i (st out : TransferV1.Acc×List Limit),applyReceipts ctx i st rs=.ok out →
      ∀r∈rs,AccountAt st.1.trie (accountKeyPath r.receiverId)
  | [],_,_,_,_,r,hr=>by simp at hr
  | r::rs,i,(acc,ls),out,h,x,hx=>by
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · obtain ⟨acc',ha,h⟩:=Sched.bind_ok h
        have hw:=system_account_write ha
        rcases List.mem_cons.mp hx with rfl|hx
        · exact written_account_at hw
        · exact account_write_back hw (native_touched_account_decode ctx rs (i+1) (acc',ls) out h x hx)
      · split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',_,h⟩:=Sched.bind_ok h
          have hw:=receipt_account_write ha
          rcases List.mem_cons.mp hx with rfl|hx
          · exact written_account_at hw
          · exact account_write_back hw (native_touched_account_decode ctx rs (i+1) (acc',ls') out h x hx)

theorem accountAt_forward {pre post : PTrie} {key : List Nat}
    (hp:WriteTreePair pre post)
    (he:(NearSpecV3.valsOf post).map accountSignature=(NearSpecV3.valsOf pre).map accountSignature)
    (ha:AccountAt pre key) : AccountAt post key := by
  obtain ⟨i,before,a,hi,hv,hd⟩:=ha
  have hx:=congrArg (fun xs=>xs[i]?) he
  simp only [List.getElem?_map,hv,Option.map_some] at hx
  cases hb:(NearSpecV3.valsOf post)[i]? with
  | none=>simp [hb] at hx
  | some after=>
    simp only [hb,Option.map_some,Option.some.injEq] at hx
    obtain ⟨b,hbdec,_⟩:=signature_decoded_before hx.symm hd
    exact ⟨i,after,b,(write_value_index hp key).symm.trans hi,hb,hbdec⟩

/-- All touched receivers still decode after the full native receipt batch;
this fact is derived even when the final write to a receiver occurred earlier. -/
theorem native_touched_final_decode {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out)
    (r : Receipt) (hr:r∈rs) : AccountAt out.1.trie (accountKeyPath r.receiverId) := by
  obtain ⟨writes,hw,_⟩:=native_sized_account_writes ctx rs i st out h
  exact accountAt_forward hw.forget.skeleton (native_receipt_signatures ctx rs i st out h)
    (native_touched_account_decode ctx rs i st out h r hr)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
