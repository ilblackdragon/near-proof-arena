import ZkFormal.NearV3.Assembly.SourcePathDigests
import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficBlock

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Near Render.SrcpGen Rcpt.Candidates

def sourceBlockOutputs (B : SrcpB) : List Msg :=
  (sourcePayloads B).map (fun p=>Render.digestMsg ⟨msgId K_SRC p.1,p.2⟩)

/-- The final computed path digest is the actual root checked by the native
verifier, not an independent SHA equality premise. -/
theorem blockOfProof_digest_chain (root : Bytes) (dup : Bool) (j q : Nat) (e : ProofEntry)
    (hv : verifyReceiptProof root e=true)
    (hp : ∀step∈e.proof.path,step.1.length=32) :
    sourceBlockOutputs (blockOfProof root dup j q e)=
      (blockOfProof root dup j q e).path.map sourceItemInput++
      [digMsg (msgId K_SRC (blockOfProof root dup j q e).qe)
        (blockOfProof root dup j q e).le (blockOfProof root dup j q e).root] := by
  have hc := proofItems_digest_chain e.proof.path q 32
    (sha256 (sha256 (u64 e.proof.toShard++encodeReceipts e.receipts)))
    (ArenaCore.sha256_length _) hp
  have hr : rootFromPath (sha256 (sha256 (u64 e.proof.toShard++encodeReceipts e.receipts))) e.proof.path=root := by
    simpa only [verifyReceiptProof,beq_iff_eq] using hv
  rw [hr] at hc
  unfold sourceItemOutput at hc
  simpa [sourceBlockOutputs,sourcePayloads,blockOfProof,List.map_map,Function.comp_def,
    sourceItemOutput,Render.digestMsg,Render.shaN,Render.ofNats,Render.toNats,digMsg,
    ArenaCore.sha256_length] using hc

/-- Logical DIGEST consumers of an honest source block partition into source
hash outputs and one RC hash output; skipped duplicates consume neither. -/
theorem blockOfProof_digest_partition (root : Bytes) (dup repeated : Bool) (j q : Nat) (e : ProofEntry)
    (hv : verifyReceiptProof root e=true)
    (hp : ∀step∈e.proof.path,step.1.length=32) :
    let B:=blockOfProof root dup j q e
    (if B.dup then [] else sourceBlockOutputs B++[digMsg (msgId K_RC B.j) B.L B.leaf]).Perm
      (DedupRender.blockMsgs B repeated B_DIGEST false) := by
  dsimp only
  have hc := blockOfProof_digest_chain root dup j q e hv hp
  cases hd : dup with
  | true => simp [blockOfProof,DedupRender.blockMsgs,DedupRender.rootMsgs,hd,B_DIGEST,B_RCL,B_SRC]
  | false =>
    change (sourceBlockOutputs (blockOfProof root false j q e)++[_]).Perm _
    have hc' := blockOfProof_digest_chain root false j q e hv hp
    rw [hc']
    simp only [DedupRender.blockMsgs,DedupRender.rootMsgs,blockOfProof,srcpLeafMsgs,srcpItemMsgs,
      sourceItemInput,B_DIGEST,B_BYTES,B_RCL,B_SRC,List.flatMap_cons,List.flatMap_nil]
    simp only [Bool.false_eq_true,ite_false,ite_true,and_true,true_and,List.nil_append,
      List.append_nil,List.singleton_append,List.cons_append]
    simp only [List.map_eq_flatMap]
    simpa [List.append_assoc,List.map_eq_flatMap,sourceItemInput] using (List.perm_append_comm (l₁ := (proofItems q 32 (sha256 (sha256 (u64 e.proof.toShard++encodeReceipts e.receipts))) e.proof.path).map sourceItemInput) (l₂ := [digMsg (msgId K_SRC (q+e.proof.path.length)) (if e.proof.path=[] then 32 else 64) (root.map UInt8.toNat), digMsg (msgId K_RC j) (u64 e.proof.toShard++encodeReceipts e.receipts).length ((sha256 (u64 e.proof.toShard++encodeReceipts e.receipts)).map UInt8.toNat)]))

end ZkFormal.NearV3.Assembly
