import ZkFormal.NearV3.Candidates.NativeAccountTrace
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountAllocationBytes

namespace ZkFormal.NearV3.Candidates.NativeAccountExecutionTrace
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- A successful bounded native receipt execution supplies its actual closing
accounts and honest account trace. IDs here belong to the receipt-stage prestate;
original-prestate rebasing is a separate obligation. -/
theorem complete {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit}
    (h : applyReceipts ctx i st rs=.ok out)
    (hn : (NearSpecV3.valsOf st.1.trie).length<ZkFormal.Algebra.P) (hr : rs.length≤8192)
    (t : Nat) (pub : List Fp) :
    ∃as,nativeAccountViews st.1.trie out.1.trie rs=some as ∧
      as.length≤rs.length ∧ (as=[] ∨ AcctWf as) ∧
      (∀M∈accountShaJobs as,∀b∈M.bytes,b<256) ∧
      TableLocal AccountEmpty.table (NativeAccountTrace.trace as) t pub ∧
      TableTraffic AccountEmpty.table.interactions (NativeAccountTrace.trace as) t pub (acctV3Traffic as) := by
  obtain ⟨as,ha,_,hlen⟩:=nativeAccountViews_success h
  have hp : rs.length<ZkFormal.Algebra.P := Nat.lt_of_le_of_lt hr (by decide)
  obtain ⟨hw,hbytes⟩:=nativeAccountViews_wf h ha hn hp
  have hb:=nativeAccountViews_bytes ha
  have ht:=NativeAccountTrace.complete as hw (Nat.le_trans hlen hr)
    (fun a hm b hmem=>hb a hm b (List.mem_append_left _ hmem)) t pub
  exact ⟨as,ha,hlen,hw,hbytes,ht⟩

end ZkFormal.NearV3.Candidates.NativeAccountExecutionTrace
