import ZkFormal.NearV3.Candidates.ProcessRepairQueryBounds
import ZkFormal.NearV3.Candidates.ProcPriorRoutedQueryAddress
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueryAddress
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)
open ProcPriorRoutedQueryAddress
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem query_address {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h68:∀seg∈AP.pubSegs,seg.bus≠68)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {r:Nat} (hr:r<tr.height 0) (ha:Live (memory tr) 0 r)
    (hq:cv (memory tr) 0 r query=1) :
    cv (memory tr) 0 r tau<33 ∧ cv (memory tr) 0 r link<4096 ∧ address (memory tr) 0 r<2^29 := by
  have ht:0<AP.tables.length := by rw [view.length];decide +kernel
  have hi:ProcPriorRoutedLastWrite.read∈AP.tables[0]!.interactions := by rw [view.wires];exact read_member
  have hh:=ProcessRepairQueryBounds.sender_bounds view hpub h68 I Ps fwd hrec hlen hns ht hr hi
    (show ProcPriorRoutedLastWrite.read.bus=68 from rfl) (show ProcPriorRoutedLastWrite.read.send=true from rfl) (read_live ha hq)
  unfold ProcPriorRoutedLastWrite.read at hh
  rw [ProcPriorCodecFamilyRead.projected_message] at hh
  change ((memory tr).cell 0 r tau).toNat<33 ∧ ((memory tr).cell 0 r link).toNat<4096 ∧
    4096*((memory tr).cell 0 r tau).toNat+((memory tr).cell 0 r link).toNat<2^29 at hh
  exact hh
end ZkFormal.NearV3.Candidates.ProcessRepairQueryAddress
