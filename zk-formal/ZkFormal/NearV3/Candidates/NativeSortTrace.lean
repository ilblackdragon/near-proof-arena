import ZkFormal.NearV3.Candidates.NativeSortIds
import ZkFormal.NearV3.Assembly.Compute
namespace ZkFormal.NearV3.Candidates.NativeSortIds
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Near.Render Assembly ZkFormal.Air ZkFormal.Algebra

def trace (rs : List Receipt) : Trace Fp:=
  if rs=[] then SortEmpty.emptyTrace else SortGeneral.trace (sorted rs)

theorem complete (rs : List Receipt) (hw:∀r∈rs,r.wf=true)
    (hd:(rs.map Receipt.receiptId).Nodup) (hn:rs.length≤8192) (t : Nat) (pub : List Fp) :
    TableLocal SortEmpty.table (trace rs) t pub := by
  by_cases he:rs=[]
  · rw [trace,if_pos he];exact SortEmpty.empty_local t pub
  · rw [trace,if_neg he]
    exact SortGeneral.complete _ ⟨by rw [length];exact List.length_pos_iff.mpr he,bytes rs hw,strict rs hw hd⟩
      (by rw [length];exact hn) t pub

theorem accepted_trace {cb wb raw : Bytes} {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w) (hr:decodeStateWitness raw=.ok w)
    (hc:checkD0a B0 cb wb=.ok ()) (hm:m.NativeValid k w) (t : Nat) (pub : List Fp) :
    TableLocal SortEmpty.table (trace (appliedReceipts k w)) t pub := by
  have hrel:RelD0a B0 cb wb:=(relD0a_iff B0 cb wb).mpr hc
  have hg:(m.ctx k).gasLimit≤maxGasLimitD0:=by
    change k.slotB2.gasLimit≤maxGasLimitD0
    simpa only [a1,hk,decide_eq_true_eq] using hrel.2.1
  have hn:=applyNewChunk_receipt_bound hm.run hg
  unfold checkD0a at hc
  obtain ⟨u,hc,_⟩:=ReexecV3D0.bind_ok' hc
  cases u
  exact complete _ (appliedReceipts_wf hr) (checkD0_applied_nodup hk hw hc) (by omega) t pub
end ZkFormal.NearV3.Candidates.NativeSortIds
