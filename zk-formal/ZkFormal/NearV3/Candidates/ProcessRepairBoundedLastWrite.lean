import ZkFormal.NearV3.Candidates.ProcessRepairLastWrite
import ZkFormal.NearV3.Candidates.ProcessRepairWriteStamp
namespace ZkFormal.NearV3.Candidates.ProcessRepairBoundedLastWrite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)
theorem consumer {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub67:∀msg,pubCount AP pub 67 true msg=0)
    (hpub68:∀msg,pubCount AP pub 68 true msg=0)
    (hpub40:∀seg∈AP.pubSegs,seg.bus≠40)
    (haddr:∀r,r<tr.height 0→Live (memory tr) 0 r→address (memory tr) 0 r<2^29)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hib:i.bus=68) (his:i.send=false)
    (him:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧ Live (memory tr) 0 q ∧ cv (memory tr) 0 q query=1 ∧
      ProcPriorVerticalReadSound.read.msgVal (memory tr) 0 q pub=i.msgVal tr tc r pub ∧
      Result (memory tr) 0 q := by
  exact ProcessRepairLastWrite.consumer view hpub68 hpub40 haddr
    (fun _ hr ha hq=>ProcessRepairWriteStamp.write_stamp view hpub67 hr ha hq) ht hr hi hib his him
end ZkFormal.NearV3.Candidates.ProcessRepairBoundedLastWrite
