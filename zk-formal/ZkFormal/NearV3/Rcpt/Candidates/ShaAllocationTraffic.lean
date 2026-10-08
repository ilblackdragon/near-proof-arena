import ZkFormal.NearV3.Rcpt.Candidates.ShaJobBridge
import ZkFormal.NearV3.Rcpt.Candidates.ReceiptByteBatch

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near

theorem jobsToSha_bytes (ms : List Render.Msg) :
    Sha.Gen.expectedBytes (jobsToSha ms)=jobBytes ms := by
  simp [Sha.Gen.expectedBytes,jobsToSha,jobBytes,emitAt,List.flatMap_map]

theorem allocated_bytes {bins : List (List Sha.Gen.Msg)} {ms : List Sha.Gen.Msg}
    (h : bins.flatten.Perm ms) :
    (bins.flatMap Sha.Gen.expectedBytes).Perm (Sha.Gen.expectedBytes ms) := by
  have hp := h.flatMap_right (fun m => (List.range m.bytes.length).map (fun p => [m.id,p,m.bytes.getD p 0]))
  have he : bins.flatMap Sha.Gen.expectedBytes=Sha.Gen.expectedBytes bins.flatten := by
    clear h hp
    induction bins with
    | nil => rfl
    | cons bin bins ih => simpa [Sha.Gen.expectedBytes,List.flatMap_append] using congrArg (List.append (Sha.Gen.expectedBytes bin)) ih
  rw [he]
  exact hp

theorem allocated_digests {bins : List (List Sha.Gen.Msg)} {ms : List Sha.Gen.Msg}
    (h : bins.flatten.Perm ms) :
    (bins.flatMap Sha.Gen.expectedDigests).Perm (Sha.Gen.expectedDigests ms) := by
  have hp := (h.filter (fun m => m.dmult)).map (fun m => [m.id,m.bytes.length]++
    (ArenaCore.sha256 (m.bytes.map UInt8.ofNat)).map UInt8.toNat)
  have he : bins.flatMap Sha.Gen.expectedDigests=Sha.Gen.expectedDigests bins.flatten := by
    clear h hp
    induction bins with
    | nil => rfl
    | cons bin bins ih => simpa [Sha.Gen.expectedDigests,List.filter_append,List.map_append] using congrArg (List.append (Sha.Gen.expectedDigests bin)) ih
  rw [he]
  exact hp

theorem fourSha_allocated_traffic (scheduler native receipt source : List Sha.Gen.Msg) :
    let bins := fourShaJobBins (fun m : Sha.Gen.Msg => (Sha.Gen.msgRows m).length)
      scheduler native receipt source
    (bins.flatMap Sha.Gen.expectedBytes).Perm
      (Sha.Gen.expectedBytes (scheduler++native++receipt++source)) ∧
    (bins.flatMap Sha.Gen.expectedDigests).Perm
      (Sha.Gen.expectedDigests (scheduler++native++receipt++source)) := by
  exact ⟨allocated_bytes (fourShaJobBins_preserve _ _ _ _ _),
    allocated_digests (fourShaJobBins_preserve _ _ _ _ _)⟩

end ZkFormal.NearV3.Rcpt.Candidates
