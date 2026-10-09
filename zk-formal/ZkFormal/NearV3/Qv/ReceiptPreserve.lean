import ZkFormal.NearV3.Qv.Preserve
import ZkFormal.NearV3.Spec.TrieOps

namespace ZkFormal.NearV3.Qv
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0

theorem applyReceipt_set {ctx : Ctx} {st out : Acc} {r : Receipt}
    (h : applyReceipt ctx st r = some out) :
    ∃ bytes, st.trie.set (accountKeyPath r.receiverId) bytes = some out.trie := by
  unfold applyReceipt at h
  dsimp only at h
  repeat first | contradiction | ((try dsimp only at h); split at h)
  all_goals
    try simp only [Option.some.injEq] at h
    subst out
    exact ⟨_,by assumption⟩

theorem applySystemReceipt_set {st out : Acc} {r : Receipt}
    (h : applySystemReceipt st r = .ok out) :
    ∃ bytes, st.trie.set (accountKeyPath r.receiverId) bytes = some out.trie := by
  unfold applySystemReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h); (try simp only [bind,Except.bind,pure,Except.pure] at h); split at h)
    | (simp only [bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h; subst out; exact ⟨_,by assumption⟩))

theorem applyReceipt_find_other {ctx : Ctx} {st out : Acc} {r : Receipt}
    (h : applyReceipt ctx st r = some out) (key : List Nat)
    (hne : key ≠ accountKeyPath r.receiverId) :
    out.trie.find key = st.trie.find key := by
  obtain ⟨bytes,hs⟩ := applyReceipt_set h
  exact PTrie.find_set_ne _ _ _ bytes _ hs hne

theorem applySystemReceipt_find_other {st out : Acc} {r : Receipt}
    (h : applySystemReceipt st r = .ok out) (key : List Nat)
    (hne : key ≠ accountKeyPath r.receiverId) :
    out.trie.find key = st.trie.find key := by
  obtain ⟨bytes,hs⟩ := applySystemReceipt_set h
  exact PTrie.find_set_ne _ _ _ bytes _ hs hne

/-- Every receipt writes only its receiver account. This covers both system
refund receipts and ordinary transfer receipts, including forwarding checks. -/
theorem applyReceipts_find_other (ctx : ApplyCtx) (key : List Nat) :
    ∀ (rs : List Receipt) (i : Nat) (st out : Acc × List Limit),
      (∀ r ∈ rs, key ≠ accountKeyPath r.receiverId) →
      applyReceipts ctx i st rs = .ok out → out.1.trie.find key = st.1.trie.find key
  | [], _, st, out, _, h => by cases h; rfl
  | r::rs, i, (acc,ls), out, hne, h => by
    have hr := hne r (by simp)
    have ht : ∀ r ∈ rs, key ≠ accountKeyPath r.receiverId :=
      fun r hm => hne r (by simp [hm])
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · obtain ⟨acc',ha,h⟩ := bind_ok' h
        exact (applyReceipts_find_other ctx key rs (i+1) (acc',ls) out ht h).trans
          (applySystemReceipt_find_other ha key hr)
      · split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',_,h⟩ := bind_ok' h
          exact (applyReceipts_find_other ctx key rs (i+1) (acc',ls') out ht h).trans
            (applyReceipt_find_other ha key hr)

theorem yield_ne_account (receiver : Bytes) : keyYieldIdx ≠ accountKeyPath receiver := by
  simp [keyYieldIdx,accountKeyPath,nibbles]

theorem applyReceipts_yield_read {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : Acc × List Limit} (h : applyReceipts ctx i st rs = .ok out) :
    out.1.trie.find keyYieldIdx = st.1.trie.find keyYieldIdx :=
  applyReceipts_find_other ctx keyYieldIdx rs i st out
    (fun r _ => yield_ne_account r.receiverId) h

theorem applyNewChunk_yield_read {ctx : ApplyCtx} {pre : PTrie}
    {rs : List Receipt} {out : MainOut} (hw : pre.wf = true)
    (h : applyNewChunk prims ctx pre rs = .ok out) :
    out.trie.find keyYieldIdx = pre.find keyYieldIdx := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨⟨mid,so⟩,hs,h⟩ := bind_ok' h
  dsimp only at h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨⟨acc,ls⟩,ha,h⟩ := bind_ok' h
  dsimp only at h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨_,_,h⟩ := bind_ok' h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst out
  exact (applyReceipts_yield_read ha).trans
    (schedStep_find_other hw hs keyYieldIdx (by decide))

/-- All validated main queue values are authenticated by the original pre-state.
This is derived from actual write preservation, not assumed read commutativity. -/
theorem applyNewChunk_pre_queue_reads {ctx : ApplyCtx} {pre : PTrie}
    {rs : List Receipt} {out : MainOut} (hw : pre.wf = true)
    (h : applyNewChunk prims ctx pre rs = .ok out) :
    ∃ v : MainValues, v.Valid ∧ v.Reads pre pre pre := by
  obtain ⟨mid,so,v,hs,hv,hr⟩ := applyNewChunk_queue_reads h
  obtain ⟨hb,hg⟩ := MainValues.pre_buffer_reads hw hs hr
  obtain ⟨hd,_,_,hy⟩ := hr
  rw [applyNewChunk_yield_read hw h] at hy
  exact ⟨v,hv,hd,hb,hg,hy⟩

end ZkFormal.NearV3.Qv
