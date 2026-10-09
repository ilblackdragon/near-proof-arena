import ZkFormal.NearV3.Candidates.PackedShaBins

namespace ZkFormal.NearV3.Candidates.PackedShaAllocation
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly Render Rcpt.Candidates

theorem selected_ok (bins : List (List Sha.Gen.Msg))
    (hok : ∀bin∈bins,Sha.MsgsOk bin) :
    ∀t∈List.range bins.length,Sha.MsgsOk (bins.getD t []) := by
  intro t ht
  have hlt:=List.mem_range.mp ht
  apply hok
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlt,Option.getD_some]
  exact List.getElem_mem hlt

/-- Allocator permutation preserves exact byte multiplicities on the common
log-22, packed-width physical SHA tables. -/
theorem bytes (bins : List (List Sha.Gen.Msg)) (jobs : List Sha.Gen.Msg)
    (hp : bins.flatten.Perm jobs) (hok : ∀bin∈bins,Sha.MsgsOk bin)
    (pub : List Fp) (msg : List Fp) :
    PackedShaBins.unionCount bins pub (List.range bins.length) false B_BYTES msg=
      ((Sha.Gen.expectedBytes jobs).map Msg.toFp).count msg := by
  rw [PackedShaBins.union_count bins pub _ (selected_ok bins hok)]
  exact NativeShaBinBalance.allocated_bytes bins jobs hp hok pub msg

theorem digests (bins : List (List Sha.Gen.Msg)) (jobs : List Sha.Gen.Msg)
    (hp : bins.flatten.Perm jobs) (hok : ∀bin∈bins,Sha.MsgsOk bin)
    (pub : List Fp) (msg : List Fp) :
    PackedShaBins.unionCount bins pub (List.range bins.length) true B_DIGEST msg=
      ((Sha.Gen.expectedDigests jobs).map Msg.toFp).count msg := by
  rw [PackedShaBins.union_count bins pub _ (selected_ok bins hok)]
  exact NativeShaBinBalance.allocated_digests bins jobs hp hok pub msg

/-- Native node/value byte senders discharge their allocated part of the packed
SHA union. Other actual producer families must still discharge the residual. -/
theorem native_bytes (ns : List NodeS3) (vs : List ValE) (hn : NodeOk ns) (hv : ValWf vs)
    (rest : List Sha.Gen.Msg) (bins : List (List Sha.Gen.Msg))
    (hp : bins.flatten.Perm (jobsToSha (nativeShaJobs ns vs)++rest))
    (hok : ∀bin∈bins,Sha.MsgsOk bin) (tn tv : Nat) (pub : List Fp) (msg : List Fp) :
    PackedShaBins.unionCount bins pub (List.range bins.length) false B_BYTES msg=
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_BYTES true msg+
      tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value vs pub) tv pub B_BYTES true msg+
      ((Sha.Gen.expectedBytes rest).map Msg.toFp).count msg := by
  rw [PackedShaBins.union_count bins pub _ (selected_ok bins hok)]
  exact NativeShaBinBalance.native_bytes ns vs hn hv rest bins hp hok tn tv pub msg

/-- A single physical allocated family has a common clock, local legality and
both byte/digest inventories for the same logical job multiset. -/
theorem complete (bins : List (List Sha.Gen.Msg)) (jobs : List Sha.Gen.Msg)
    (hp : bins.flatten.Perm jobs) (hok : ∀bin∈bins,Sha.MsgsOk bin) (pub : List Fp) :
    (∀t,(PackedShaBins.trace bins).log t=22) ∧
    (∀t∈List.range bins.length,
      TableLocal (ShaCarryKinds.table B_BYTES B_DIGEST) (PackedShaBins.trace bins) t pub) ∧
    (∀msg,PackedShaBins.unionCount bins pub (List.range bins.length) false B_BYTES msg=
      ((Sha.Gen.expectedBytes jobs).map Msg.toFp).count msg) ∧
    (∀msg,PackedShaBins.unionCount bins pub (List.range bins.length) true B_DIGEST msg=
      ((Sha.Gen.expectedDigests jobs).map Msg.toFp).count msg) := by
  refine ⟨PackedShaBins.clock bins,?_,bytes bins jobs hp hok pub,digests bins jobs hp hok pub⟩
  intro t ht
  exact PackedShaBins.complete bins t pub (selected_ok bins hok t ht)

end ZkFormal.NearV3.Candidates.PackedShaAllocation
