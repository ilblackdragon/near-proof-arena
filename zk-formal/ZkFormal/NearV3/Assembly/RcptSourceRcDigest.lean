import ZkFormal.NearV3.Assembly.RcptSourceInputs
import ZkFormal.NearV3.Rcpt.Candidates.ShaJobBridge

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near Rcpt.Candidates Render.SrcpGen

/-- The source compiler's actual RC request is the native list hash, at the
same public occurrence index. Duplicate gating remains outside this equation. -/
theorem source_block_rc_digest {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (j : Nat) (hj : j<p.lists.length) :
    let B:=DedupCompile.block p.lists w.entries j
    digMsg (msgId K_RC B.j) B.L B.leaf = Render.digestMsg
      ⟨msgId K_RC j,(u64 k.H.shardId++encodeReceipts
        (sourceEntry w.entries (p.lists.getD j ⟨[],0,[]⟩)).receipts).map UInt8.toNat⟩ := by
  have hm : p.lists.getD j ⟨[],0,[]⟩∈p.lists := by
    rw [←List.getElem_eq_getD (h:=hj) ⟨[],0,[]⟩]
    exact List.getElem_mem hj
  have ht := sourceInputLists_toShard ha hp hk hw _ hm
  change digMsg (msgId K_RC j)
    (u64 (sourceEntry w.entries (p.lists.getD j ⟨[],0,[]⟩)).proof.toShard++encodeReceipts
      (sourceEntry w.entries (p.lists.getD j ⟨[],0,[]⟩)).receipts).length
    ((sha256 (u64 (sourceEntry w.entries (p.lists.getD j ⟨[],0,[]⟩)).proof.toShard++encodeReceipts
      (sourceEntry w.entries (p.lists.getD j ⟨[],0,[]⟩)).receipts)).map UInt8.toNat)=_
  rw [ht]
  simp [Render.digestMsg,Render.shaN,Render.ofNats,Render.toNats,digMsg,List.map_map,Function.comp_def]

end ZkFormal.NearV3.Assembly.RcptSkeleton
