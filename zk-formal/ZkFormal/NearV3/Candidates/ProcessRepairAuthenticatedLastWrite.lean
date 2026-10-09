import ZkFormal.NearV3.Candidates.ProcessRepairPreparedLastWrite
import ZkFormal.NearV3.Candidates.ProcessRepairWriteAddress
import ZkFormal.NearV3.Candidates.ProcessRepairQueryAddress
import ZkFormal.NearV3.Candidates.ProcPriorPublicSenderBound
namespace ZkFormal.NearV3.Candidates.ProcessRepairAuthenticatedLastWrite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)
theorem consumer {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub67:∀msg,pubCount AP pub 67 true msg=0)
    (hpub68:∀msg,pubCount AP pub 68 true msg=0)
    (hpub40:∀seg∈AP.pubSegs,seg.bus≠40)
    (hpar:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h68:∀seg∈AP.pubSegs,seg.bus≠68)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    (hpub70:∀msg,pubCount AP pub 70 true msg=0)
    (hpub72:∀msg,pubCount AP pub 72 true msg=0)
    (hpub76:∀msg,pubCount AP pub 76 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hib:i.bus=68) (his:i.send=false)
    (him:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧ Live (memory tr) 0 q ∧ cv (memory tr) 0 q query=1 ∧
      ProcPriorVerticalReadSound.read.msgVal (memory tr) 0 q pub=i.msgVal tr tc r pub ∧
      Result (memory tr) 0 q := by
  apply ProcessRepairPreparedLastWrite.consumer view hpub67 hpub68 hpub40 hpar h68 I hp fwd hrec
    (fun q hq ha hz=> (ProcessRepairWriteAddress.write_address view hpar hpub67 hpub70 hpub72 hpub76
      I hp fwd hrec hq ha hz).2.2) ht hr hi hib his him
end ZkFormal.NearV3.Candidates.ProcessRepairAuthenticatedLastWrite
