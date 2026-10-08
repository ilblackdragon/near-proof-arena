import ZkFormal.NearV3.Assembly.ShaMessagePlacement

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Sha.Gen
open Rcpt.Candidates Rcpt.Candidates.DedupCompile

def sourceShaPayload (payload : Nat × List Nat) : Msg :=
  ⟨ZkFormal.Near.msgId K_SRC payload.1,payload.2,true⟩

def sourceShaMessages (sources : List SrcList) (entries : List ProofEntry) : List Msg :=
  ((blocks sources entries).filter fun B => !B.dup).flatMap fun B =>
    (sourcePayloads B).map sourceShaPayload

theorem sha_rows_eq_receipt_weight (M : Msg) :
    (msgRows M).length=Rcpt.msgRows M.bytes.length := by
  have hn := ZkFormal.Sha.Complete.nb_eq M
  rw [sha_message_rows]
  unfold Rcpt.msgRows
  have hm : M.bytes.length%64<64 := Nat.mod_lt _ (by decide)
  omega

theorem sourceShaMessages_weights (sources : List SrcList) (entries : List ProofEntry) :
    upsertShaWeights (sourceShaMessages sources entries)=sourceWeights sources entries := by
  simp only [upsertShaWeights,sourceShaMessages,sourceWeights,payloadWeights,
    List.map_flatMap,List.map_map,Function.comp_def,sha_rows_eq_receipt_weight,sourceShaPayload]

/-- Concrete message placement preserves every original source message ID and byte.
No source SHA message is duplicated, dropped, or split by the allocator. -/
theorem checkD0a_source_sha_messages {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hr : decodeStateWitness raw=.ok w) :
    let bins := sourceShaMessageBins (sourceShaMessages p.lists w.entries)
    bins.length=3 ∧ bins.flatten=sourceShaMessages p.lists w.entries ∧
      (∀ bin∈bins,(honestRows bin).length≤2^22) := by
  have hrel := (relD0a_iff B0 cb wb).mpr hc
  obtain ⟨_,_,hs⟩ := relD0a_inputs hrel hp hf hr
  obtain ⟨he,hm⟩ := sourceWeights_exact hr p.lists hs
  have hb := (relD0a_work_bounds hrel hp hf hr).2.1
  refine ⟨by simp [sourceShaMessageBins],sourceShaMessageBins_reconstruct _,?_⟩
  apply sourceShaMessageBins_fit
  · rw [sourceShaMessages_weights];exact hm
  · rw [←upsertShaWeights_sum,sourceShaMessages_weights,he]
    exact hb

end ZkFormal.NearV3.Assembly
