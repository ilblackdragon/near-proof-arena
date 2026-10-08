import ZkFormal.NearV3.Candidates.NativePostShaTraffic
import ZkFormal.NearV3.Assembly.ShaBinExact

namespace ZkFormal.NearV3.Candidates.NativeShaBinBalance
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Assembly Rcpt.Candidates

/-- Physical SHA tables consume the exact allocated byte multiset. This permits
arbitrary job reordering across bins without discarding repeated identifiers. -/
theorem allocated_bytes (bins : List (List Sha.Gen.Msg)) (jobs : List Sha.Gen.Msg)
    (hp : bins.flatten.Perm jobs) (hok : ∀bin∈bins,Sha.MsgsOk bin)
    (pub : List Fp) (msg : List Fp) :
    shaUnionCount (shaBinTrace bins) pub (List.range bins.length) false B_BYTES msg=
      ((Sha.Gen.expectedBytes jobs).map Msg.toFp).count msg := by
  have ht := (shaBinUnion_traffic bins pub hok B_BYTES msg).2
  simp only [shaBinTraffic,ite_true] at ht
  rw [ht]
  exact ((Rcpt.Candidates.allocated_bytes hp).map Msg.toFp).count_eq msg

/-- Digest multiplicities follow the same allocation, including each job's
digest-enable flag; duplicate IDs are not silently merged. -/
theorem allocated_digests (bins : List (List Sha.Gen.Msg)) (jobs : List Sha.Gen.Msg)
    (hp : bins.flatten.Perm jobs) (hok : ∀bin∈bins,Sha.MsgsOk bin)
    (pub : List Fp) (msg : List Fp) :
    shaUnionCount (shaBinTrace bins) pub (List.range bins.length) true B_DIGEST msg=
      ((Sha.Gen.expectedDigests jobs).map Msg.toFp).count msg := by
  have ht := (shaBinUnion_traffic bins pub hok B_DIGEST msg).1
  simp only [shaBinTraffic,ite_true] at ht
  rw [ht]
  exact ((Rcpt.Candidates.allocated_digests hp).map Msg.toFp).count_eq msg

/-- The actual native node/value tables discharge their part of physical SHA
byte consumption. Other families remain as an explicit residual inventory. -/
theorem native_bytes (ns : List NodeS3) (vs : List ValE) (hn : NodeOk ns) (hv : ValWf vs)
    (rest : List Sha.Gen.Msg) (bins : List (List Sha.Gen.Msg))
    (hp : bins.flatten.Perm (jobsToSha (nativeShaJobs ns vs)++rest))
    (hok : ∀bin∈bins,Sha.MsgsOk bin) (tn tv : Nat) (pub : List Fp) (msg : List Fp) :
    shaUnionCount (shaBinTrace bins) pub (List.range bins.length) false B_BYTES msg=
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_BYTES true msg+
      tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value vs pub) tv pub B_BYTES true msg+
      ((Sha.Gen.expectedBytes rest).map Msg.toFp).count msg := by
  rw [allocated_bytes bins _ hp hok pub msg,NativePostShaTraffic.bytes ns vs hn hv tn tv pub msg]
  simp only [Sha.Gen.expectedBytes,List.flatMap_append,List.map_append,List.count_append]

end ZkFormal.NearV3.Candidates.NativeShaBinBalance
