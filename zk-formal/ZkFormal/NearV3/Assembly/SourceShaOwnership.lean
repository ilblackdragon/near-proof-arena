import ZkFormal.NearV3.Assembly.SourceShaMessages

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Sha.Gen Render.SrcpGen
open Rcpt.Candidates Rcpt.Candidates.DedupCompile

theorem blockOfProof_payload_id (root : Bytes) (dup : Bool) (j q : Nat) (e : ProofEntry)
    {payload : Nat×List Nat} (hp : payload∈sourcePayloads (blockOfProof root dup j q e)) :
    payload.1≤q+e.proof.path.length := by
  simp only [sourcePayloads,List.mem_append,List.mem_singleton,List.mem_map] at hp
  rcases hp with rfl|⟨it,hi,rfl⟩
  · simp [blockOfProof]
  · obtain ⟨i,hi',he⟩ := List.mem_iff_getElem.mp hi
    have hidx := proofItems_indices e.proof.path q 32 (sha256 (sha256 (u64 e.proof.toShard ++ encodeReceipts e.receipts))) i hi'
    simp only [blockOfProof] at he
    have hq : it.q=q+1+i := by grind only
    simp only [blockOfProof,proofItems_length] at hi'
    simp only [Prod.fst]
    omega

theorem checkD0a_source_message_ids {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hr : decodeStateWitness raw=.ok w)
    {M : ZkFormal.Sha.Gen.Msg} (hm : M∈sourceShaMessages p.lists w.entries) :
    M.id<ZkFormal.Algebra.P ∧ M.id%16=13 := by
  obtain ⟨B,hB,hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨payload,hpayload,rfl⟩ := List.mem_map.mp hm
  obtain ⟨hB,hdup⟩ := List.mem_filter.mp hB
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hB
  have hj' := List.mem_range.mp hj
  have hd : Public.sourceDup p.lists j=false := by
    cases hd : Public.sourceDup p.lists j <;> simp_all [block,blockOfProof]
  have hqid := blockOfProof_payload_id _ _ _ _ _ hpayload
  have hend := computed_end p.lists w.entries j hd
  have hnext := (relD0a_counter_bound ((relD0a_iff B0 cb wb).mpr hc) hp hf hr (by omega : j+1≤p.lists.length)).1
  simp only [block,blockOfProof] at hend
  simp only [sourceShaPayload,msgId,K_SRC,ZkFormal.Algebra.P]
  constructor <;> omega

end ZkFormal.NearV3.Assembly
