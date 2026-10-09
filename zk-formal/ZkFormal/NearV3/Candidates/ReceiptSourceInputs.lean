import ZkFormal.NearV3.Assembly.RcptSourceInputs
import ZkFormal.NearV3.Assembly.RcptNativeNamed
import ZkFormal.NearV3.Assembly.ReceiptWellformed
import ZkFormal.NearV3.Assembly.RcptGasPriceBound
import ZkFormal.NearV3.Rcpt.Candidates.DedupActualTraffic

namespace ZkFormal.NearV3.Candidates.ReceiptSourceInputs
open NearSpec NearSpecV3 Sched ZkFormal.Near Assembly RcptSkeleton Rcpt.Candidates

theorem admitted {budget : Nat} {cb wb raw : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness} (ctx : ApplyCtx)
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hk : walkD0 cb=.ok k) (hd : decodeW wb=.ok w) (hw : decodeStateWitness raw=.ok w) :
    let lists:=sourceInputLists ctx p.lists w.entries
    lists.length=p.lists.length ∧ lists.flatten.map Input.receipt=appliedReceipts k w ∧
    (∀xs∈lists,∀x∈xs,x.receipt.wf=true) ∧ lists≠[] ∧
    (∀xs∈lists,∀x∈xs,AccountId.isNamed x.receipt.receiverId=true) ∧
    (∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt) := by
  dsimp only
  have he:=sourceInputLists_applied ctx ha hp hk hd
  have hmem : ∀xs∈sourceInputLists ctx p.lists w.entries,∀x∈xs,x.receipt∈appliedReceipts k w := by
    intro xs hxs x hx
    rw [←he]
    exact List.mem_map.mpr ⟨x,List.mem_flatten.mpr ⟨xs,hxs,hx⟩,rfl⟩
  refine ⟨sourceInputLists_length _ _ _,he,?_,?_,?_,?_⟩
  · intro xs hxs x hx
    exact appliedReceipts_wf hw _ (hmem xs hxs x hx)
  · intro hz
    have hlen:=sourceInputLists_length ctx p.lists w.entries
    rw [hz] at hlen
    have hn : p.lists=[] := List.length_eq_zero_iff.mp hlen.symm
    have hb:=DedupCompile.relD0a_blocks_nonempty ha hp w.entries
    simp [DedupCompile.blocks,hn] at hb
  · intro xs hxs x hx
    exact appliedReceipts_named hw _ (hmem xs hxs x hx)
  · exact nativeInputs_flags _ _

theorem gas {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hk : walkD0 cb=.ok k) (hm : m.NativeValid k w) :
    (m.ctx k).gasLimit≤maxGasLimitD0 ∧ (m.ctx k).gasPrice<256^16 := by
  refine ⟨?_,prepD0_native_gasPrice_bound hp hk hm⟩
  change k.slotB2.gasLimit≤maxGasLimitD0
  simpa only [a1,hk,decide_eq_true_eq] using ha.2.1

end ZkFormal.NearV3.Candidates.ReceiptSourceInputs
