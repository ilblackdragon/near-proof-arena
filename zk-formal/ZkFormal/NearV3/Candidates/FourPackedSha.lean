import ZkFormal.NearV3.Candidates.PackedShaAllocation

namespace ZkFormal.NearV3.Candidates.FourPackedSha
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly Rcpt.Candidates

def bins (scheduler native receipt source : List Sha.Gen.Msg) : List (List Sha.Gen.Msg) :=
  fourShaJobBins (fun m : Sha.Gen.Msg=>(Sha.Gen.msgRows m).length) scheduler native receipt source

/-- Moving whole jobs to bins retains their byte-range contract without any
identifier uniqueness assumption. Length bounds follow from physical capacity. -/
theorem allocated_ok (bs : List (List Sha.Gen.Msg)) (jobs : List Sha.Gen.Msg)
    (hp : bs.flatten.Perm jobs)
    (hb : ∀M∈jobs,∀b∈M.bytes,b<256)
    (hr : ∀bin∈bs,(Sha.Gen.honestRows bin).length≤2^22) :
    ∀bin∈bs,Sha.MsgsOk bin := by
  intro bin hbin
  refine ⟨?_,fun M hm=>sha_message_len_of_rows (hr bin hbin) hm,hr bin hbin⟩
  intro M hm b hbyte
  exact hb M (hp.mem_iff.mp (List.mem_flatten.mpr ⟨bin,hbin,hm⟩)) b hbyte

/-- The executable four-bin allocator supplies the full SHA renderer contract
from the four family budgets and valid original byte payloads. -/
theorem allocation (scheduler native receipt source : List Sha.Gen.Msg)
    (hs : (Sha.Gen.honestRows scheduler).length≤1663260)
    (hn : (Sha.Gen.honestRows native).length≤2925275)
    (hr : (Sha.Gen.honestRows receipt).length≤1373299)
    (hp : (Sha.Gen.honestRows source).length≤8932712)
    (hm : ∀M∈source,(Sha.Gen.msgRows M).length≤35)
    (hb : ∀M∈scheduler++native++receipt++source,∀b∈M.bytes,b<256) :
    (bins scheduler native receipt source).length=4 ∧
    (bins scheduler native receipt source).flatten.Perm (scheduler++native++receipt++source) ∧
    ∀bin∈bins scheduler native receipt source,Sha.MsgsOk bin := by
  obtain ⟨hcount,hfit,hperm⟩:=fourSha_physical_fit scheduler native receipt source hs hn hr hp hm
  exact ⟨hcount,hperm,allocated_ok _ _ hperm hb hfit⟩

/-- Exactly four packed physical tables at one clock, with both bus inventories
bound to the original full job objects, including digest-enable flags. -/
theorem complete (scheduler native receipt source : List Sha.Gen.Msg)
    (hs : (Sha.Gen.honestRows scheduler).length≤1663260)
    (hn : (Sha.Gen.honestRows native).length≤2925275)
    (hr : (Sha.Gen.honestRows receipt).length≤1373299)
    (hp : (Sha.Gen.honestRows source).length≤8932712)
    (hm : ∀M∈source,(Sha.Gen.msgRows M).length≤35)
    (hb : ∀M∈scheduler++native++receipt++source,∀b∈M.bytes,b<256) (pub : List Fp) :
    let bs:=bins scheduler native receipt source
    bs.length=4 ∧ (∀t,(PackedShaBins.trace bs).log t=22) ∧
    (∀t∈List.range 4,TableLocal (ShaCarryKinds.table B_BYTES B_DIGEST) (PackedShaBins.trace bs) t pub) ∧
    (∀msg,PackedShaBins.unionCount bs pub (List.range 4) false B_BYTES msg=
      ((Sha.Gen.expectedBytes (scheduler++native++receipt++source)).map Msg.toFp).count msg) ∧
    (∀msg,PackedShaBins.unionCount bs pub (List.range 4) true B_DIGEST msg=
      ((Sha.Gen.expectedDigests (scheduler++native++receipt++source)).map Msg.toFp).count msg) := by
  obtain ⟨hc,hperm,hok⟩:=allocation scheduler native receipt source hs hn hr hp hm hb
  have hh:=PackedShaAllocation.complete _ _ hperm hok pub
  rw [hc] at hh
  exact ⟨hc,hh⟩

end ZkFormal.NearV3.Candidates.FourPackedSha
