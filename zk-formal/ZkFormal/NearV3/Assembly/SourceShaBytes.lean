import ZkFormal.NearV3.Assembly.SourceSchedulerShaMessages

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Sha.Gen Render.SrcpGen
open Rcpt.Candidates Rcpt.Candidates.DedupCompile

private theorem natBytes_lt (bs : Bytes) : ∀b∈bs.map UInt8.toNat,b<256 := by
  intro b hb
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
  exact v.toNat_lt

theorem proofItems_byte_bounds (path : List (Bytes×Nat)) (q len : Nat) (acc : Bytes) :
    ∀it∈proofItems q len acc path,∀b∈it.bytes,b<256 := by
  induction path generalizing q len acc with
  | nil => simp [proofItems]
  | cons step rest ih =>
    intro it hi b hb
    simp only [proofItems,List.mem_cons] at hi
    rcases hi with rfl|hi
    · simp only [SrcpItem.bytes] at hb
      split at hb
      all_goals
        rcases List.mem_append.mp hb with hb|hb
        exact natBytes_lt _ b hb
        exact natBytes_lt _ b hb
    · exact ih _ _ _ it hi b hb

theorem sourceShaMessages_bytes (sources : List SrcList) (entries : List ProofEntry) :
    ∀M∈sourceShaMessages sources entries,∀b∈M.bytes,b<256 := by
  intro M hM b hb
  obtain ⟨B,hB,hM⟩ := List.mem_flatMap.mp hM
  obtain ⟨payload,hpayload,rfl⟩ := List.mem_map.mp hM
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp (List.mem_filter.mp hB).1
  simp only [sourcePayloads,List.mem_append,List.mem_singleton,List.mem_map] at hpayload
  rcases hpayload with rfl|⟨it,hit,rfl⟩
  · exact natBytes_lt _ b hb
  · exact proofItems_byte_bounds _ _ _ _ it hit b hb

/-- The existing physical-row cap also bounds every message's byte length.
No independent preimage-size premise is needed once this row bound is known. -/
theorem sha_message_len_of_rows {ms : List Msg}
    (hr : (honestRows ms).length≤2^22) {M : Msg} (hm : M∈ms) : M.bytes.length<2^25 := by
  have hrow : (msgRows M).length≤(honestRows ms).length := by
    clear hr
    induction ms with
    | nil => simp at hm
    | cons N ns ih =>
      rcases List.mem_cons.mp hm with rfl|hm
      · simp [honestRows]
      · have hh := ih hm
        simp only [honestRows,List.flatMap_cons,List.length_append] at *
        omega
  have hn := ZkFormal.Sha.Complete.nb_eq M
  rw [sha_message_rows] at hrow
  omega

end ZkFormal.NearV3.Assembly
