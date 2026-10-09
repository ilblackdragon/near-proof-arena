import ZkFormal.NearV3.Assembly.ReceiptShape
import ZkFormal.NearV3.Rcpt.Candidates.AccountShaJobs

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0

/-- Exact native account writes, including repeated writes to the same receiver. -/
inductive AccountWriteRun : PTrie→List (List Nat×Bytes)→PTrie→Prop
  | nil (t : PTrie) : AccountWriteRun t [] t
  | cons {t mid out : PTrie} {key : List Nat} {bytes : Bytes} {rest : List (List Nat×Bytes)}
      (write : t.set key bytes=some mid) (tail : AccountWriteRun mid rest out) :
      AccountWriteRun t ((key,bytes)::rest) out

/-- Successful native processing performs exactly one account write per receipt,
for system receipts as well as ordinary transfers. -/
theorem native_account_writes (ctx : ApplyCtx) :
    ∀rs i (st out : Acc×List Limit), applyReceipts ctx i st rs=.ok out →
    ∃writes, AccountWriteRun st.1.trie writes out.1.trie ∧
      writes.map Prod.fst=rs.map (fun r => accountKeyPath r.receiverId)
  | [],_,st,out,h => by cases h; exact ⟨[],.nil _,rfl⟩
  | r::rs,i,(acc,ls),out,h => by
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · obtain ⟨acc',ha,h⟩ := bind_ok' h
        obtain ⟨bytes,hs⟩ := Qv.applySystemReceipt_set ha
        obtain ⟨writes,hr,hk⟩ := native_account_writes ctx rs (i+1) (acc',ls) out h
        exact ⟨(accountKeyPath r.receiverId,bytes)::writes,.cons hs hr,by simp [hk]⟩
      · split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',_,h⟩ := bind_ok' h
          obtain ⟨bytes,hs⟩ := Qv.applyReceipt_set ha
          obtain ⟨writes,hr,hk⟩ := native_account_writes ctx rs (i+1) (acc',ls') out h
          exact ⟨(accountKeyPath r.receiverId,bytes)::writes,.cons hs hr,by simp [hk]⟩

/-- Last-occurrence order is useful for allocating one closing account record
per touched key after its final receipt write. -/
def distinctTouched : List (List Nat)→List (List Nat)
  | [] => []
  | k::ks => if k∈ks then distinctTouched ks else k::distinctTouched ks

theorem distinctTouched_mem (k : List Nat) : ∀ks,k∈distinctTouched ks ↔ k∈ks
  | [] => by simp [distinctTouched]
  | a::ks => by
    simp only [distinctTouched]
    split <;> simp_all [List.mem_cons,distinctTouched_mem k ks]

theorem distinctTouched_nodup : ∀ks,(distinctTouched ks).Nodup
  | [] => by simp [distinctTouched]
  | k::ks => by
    simp only [distinctTouched]
    split
    · exact distinctTouched_nodup ks
    · exact List.nodup_cons.mpr ⟨by simpa only [distinctTouched_mem] using ‹k∉ks›,distinctTouched_nodup ks⟩

theorem distinctTouched_count : ∀ks,(distinctTouched ks).length≤ks.length
  | [] => by simp [distinctTouched]
  | k::ks => by
    have h := distinctTouched_count ks
    simp only [distinctTouched,List.length_cons]
    split <;> (try simp only [List.length_cons]) <;> omega

/-- The canonical unique account-key allocation is paid for by actual native
receipt execution; linking these keys to an AIR account renderer is separate. -/
theorem native_touched_count {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : Acc×List Limit} (h : applyReceipts ctx i st rs=.ok out) :
    ∃writes, AccountWriteRun st.1.trie writes out.1.trie ∧
      writes.length=rs.length ∧
      (distinctTouched (writes.map Prod.fst)).Nodup ∧
      (distinctTouched (writes.map Prod.fst)).length≤rs.length ∧
      (∀key,key∈distinctTouched (writes.map Prod.fst) ↔
        key∈rs.map (fun r => accountKeyPath r.receiverId)) := by
  obtain ⟨writes,hr,hk⟩ := native_account_writes ctx rs i st out h
  have hl := congrArg List.length hk
  simp only [List.length_map] at hl
  refine ⟨writes,hr,hl,distinctTouched_nodup _,?_,?_⟩
  · have hh := distinctTouched_count (writes.map Prod.fst)
    simpa only [List.length_map,hl] using hh
  · intro key
    rw [distinctTouched_mem,hk]

/-- Extract the actual receipt stage inside the successful main runtime, after
its queue/scheduler setup. No correspondence to an invented replay is assumed. -/
theorem newchunk_touched {ctx : ApplyCtx} {t : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx t rs=.ok out) :
    ∃before after : Acc×List Limit, ∃writes,
      applyReceipts ctx 0 before rs=.ok after ∧
      AccountWriteRun before.1.trie writes after.1.trie ∧
      writes.length=rs.length ∧ (distinctTouched (writes.map Prod.fst)).Nodup ∧
      (distinctTouched (writes.map Prod.fst)).length≤rs.length ∧
      (∀key,key∈distinctTouched (writes.map Prod.fst) ↔
        key∈rs.map (fun r => accountKeyPath r.receiverId)) := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨⟨_,so⟩,_,h⟩ := bind_ok' h
  dsimp only at h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨after,ha,_⟩ := bind_ok' h
  obtain ⟨writes,hr,hl,hn,hc,hkeys⟩ := native_touched_count ha
  exact ⟨_,after,writes,ha,hr,hl,hn,hc,hkeys⟩

end ZkFormal.NearV3.Rcpt.Candidates
