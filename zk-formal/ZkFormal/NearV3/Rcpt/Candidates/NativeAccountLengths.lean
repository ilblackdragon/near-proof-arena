import ZkFormal.NearV3.Rcpt.Candidates.NativeWriteLookup
import ZkFormal.Near.Spec.SoundAccount

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0 ZkFormal.Near

theorem decoded_account_write_length {raw : Bytes} {a : Account}
    (h : Account.decode raw=some a) (amount : Nat) :
    raw.length=72 ∧ (Account.encode {a with amount:=amount}).length=raw.length := by
  have hw := Sound.decode_wf h
  exact ⟨hw.2.2.2.2,(Sound.account_encode_length _ hw.2.2.1).trans hw.2.2.2.2.symm⟩

theorem native_receipt_write_length {ctx : Ctx} {st out : Acc} {r : Receipt}
    (h : applyReceipt ctx st r=some out) :
    ∃raw bytes, st.trie.get (accountKeyPath r.receiverId)=some raw ∧
      raw.length=72 ∧ bytes.length=raw.length ∧
      st.trie.set (accountKeyPath r.receiverId) bytes=some out.trie := by
  unfold applyReceipt at h
  dsimp only at h
  repeat first | contradiction | ((try dsimp only at h); split at h)
  all_goals
    try simp only [Option.some.injEq] at h
    subst out
    refine ⟨_,_,by assumption,?_,?_,by assumption⟩
    · exact (decoded_account_write_length (by assumption) 0).1
    · exact (decoded_account_write_length (by assumption) _).2

theorem native_system_write_length {st out : Acc} {r : Receipt}
    (h : applySystemReceipt st r=.ok out) :
    ∃raw bytes, st.trie.find (accountKeyPath r.receiverId)=some (some raw) ∧
      raw.length=72 ∧ bytes.length=raw.length ∧
      st.trie.set (accountKeyPath r.receiverId) bytes=some out.trie := by
  unfold applySystemReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h); (try simp only [bind,Except.bind,pure,Except.pure] at h); split at h)
    | (simp only [bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h; subst out))
  all_goals
    refine ⟨_,_,by assumption,?_,?_,by assumption⟩
    · exact (decoded_account_write_length (by assumption) 0).1
    · exact (decoded_account_write_length (by assumption) _).2

end ZkFormal.NearV3.Rcpt.Candidates
