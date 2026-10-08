import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountView
import ZkFormal.NearV3.Assembly.RcptDepositLedger
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 NearSpec.TransferV1 ZkFormal.Near Assembly.RcptSkeleton

/-- Actual account write, retaining the decoded original bytes and the final
amount rather than weakening the write to a length-only relation. -/
def NativeAccountWrite (st out : Acc) (r : Receipt) : Prop :=
  ∃raw a,st.trie.get (accountKeyPath r.receiverId)=some raw ∧ Account.decode raw=some a ∧
    a.amount+r.deposit<Params.u128Max ∧
    st.trie.set (accountKeyPath r.receiverId) ({a with amount:=a.amount+r.deposit}.encode)=some out.trie

theorem receipt_account_write {ctx : Ctx} {st out : Acc} {r : Receipt}
    (h : applyReceipt ctx st r=some out) : NativeAccountWrite st out r := by
  unfold applyReceipt at h
  dsimp only at h
  repeat first | contradiction | ((try dsimp only at h);split at h)
  all_goals
    try simp only [Option.some.injEq] at h
    subst out
    exact ⟨_,_,by assumption,by assumption,by omega,by assumption⟩

theorem system_account_write {st out : Acc} {r : Receipt}
    (h : applySystemReceipt st r=.ok out) : NativeAccountWrite st out r := by
  unfold applySystemReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h);(try simp only [bind,Except.bind,pure,Except.pure] at h);split at h)
    | (simp only [bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h;subst out))
  all_goals
    refine ⟨_,_,?_,by assumption,by omega,by assumption⟩
    rw [native_get_find,show st.trie.find (accountKeyPath r.receiverId)=some (some _) from by assumption]
    rfl

theorem native_step_account_write {ctx : ApplyCtx} {st out : Acc} {r : Receipt}
    (h : nativeReceiptStep ctx st r=some out) : NativeAccountWrite st out r := by
  unfold nativeReceiptStep at h
  split at h
  · cases hs:applySystemReceipt st r with
    | error e=>simp [hs] at h
    | ok next=>simp only [hs,Option.some.injEq] at h;subst out;exact system_account_write hs
  · exact receipt_account_write h

theorem ledger_account_write {ctx : ApplyCtx} {s : NativeDepositStep} (h:s.Valid ctx) :
    s.before.trie.set (accountKeyPath s.receipt.receiverId)
      ({s.account with amount:=s.account.amount+s.receipt.deposit}.encode)=some s.after.trie := by
  obtain ⟨raw,a,hr,hd,_,hs⟩:=native_step_account_write h.2
  obtain ⟨old,ho,ha⟩:=h.1.raw
  have he:raw=old:=Option.some.inj (hr.symm.trans ho)
  subst raw
  have he':a=s.account:=Option.some.inj (hd.symm.trans ha)
  subst a
  exact hs

/-- Every ledger step provides a byte-faithful account view whose SHA payload
is exactly the native write. The slot ID/closing version allocator is separate. -/
theorem ledger_account_view {ctx : ApplyCtx} {s : NativeDepositStep} (h:s.Valid ctx)
    (vid closing : Nat) (hk:vid<Algebra.P) (ht:closing<Algebra.P) :
    ∃raw, s.before.trie.get (accountKeyPath s.receipt.receiverId)=some raw ∧
      AcctWf [nativeAccountView vid closing raw (s.account.amount+s.receipt.deposit)] ∧
      s.before.trie.set (accountKeyPath s.receipt.receiverId)
        ({s.account with amount:=s.account.amount+s.receipt.deposit}.encode)=some s.after.trie ∧
      ∀m∈accountShaJobs [nativeAccountView vid closing raw (s.account.amount+s.receipt.deposit)],
        ∀x∈m.bytes,x<256 := by
  obtain ⟨raw,hr,hd⟩:=h.1.raw
  exact ⟨raw,hr,nativeAccountView_wf vid closing hk ht hd _,ledger_account_write h,nativeAccountView_job_bytes vid closing raw _⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
