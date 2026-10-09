import ZkFormal.NearV3.Candidates.ProcessRepairWriteFrame
import ZkFormal.NearV3.Candidates.ProcessRepairAuthenticatedLastWrite
import ZkFormal.NearV3.Candidates.ProcessRepairPreparedLastWrite
import ZkFormal.NearV3.Candidates.ProcessRepairWriteAddress
import ZkFormal.NearV3.Candidates.ProcessRepairQueryAddress
import ZkFormal.NearV3.Candidates.ProcPriorPublicSenderBound
namespace ZkFormal.NearV3.Candidates.ProcessRepairEmptyPriorRead
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)
theorem consumer {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub67:∀msg,pubCount AP pub 67 true msg=0)
    (hpub75:∀msg,pubCount AP pub 75 true msg=0)
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
      ∀f,f<tr.height 0→cv (ProcPriorRoutedRawSource.raw tr) 0 f (ProcPriorVertical4Linear.stage 2)=1→
        cv (ProcPriorRoutedRawSource.raw tr) 0 f ProcPriorRawFrame.first=1→
        (cv (ProcPriorRoutedRawSource.raw tr) 0 f ProcPriorRawFrame.count=0 ∨
         cv (ProcPriorRoutedRawSource.raw tr) 0 f ProcPriorRawFrame.present=0)→
        cv (memory tr) 0 q tau=cv (ProcPriorRoutedRawSource.raw tr) 0 f ProcPriorRawFrame.tau→
        cv (memory tr) 0 q lo=0 ∧ cv (memory tr) 0 q ProcPriorMemoryTable.hi=0 := by
  obtain ⟨q,hq,hqa,hqq,hmsg,hresult⟩:=ProcessRepairAuthenticatedLastWrite.consumer view hpub67 hpub68 hpub40 hpar h68
    I hp fwd hrec hpub70 hpub72 hpub76 ht hr hi hib his him
  refine ⟨q,hq,hqa,hqq,hmsg,?_⟩
  intro f hf hfs hff hz hqt
  have hc:cv (ProcPriorRoutedRawSource.raw tr) 0 f ProcPriorRawFrame.count=0:=by
    rcases hz with hz|hz
    · exact hz
    · exact (ProcPriorRawSound.absent_zero (ProcessRepairRawBytes.overlay_local view) hf hfs hz).2
  rcases hresult with hzero|⟨w,hqw,hwa,hwq,haddr,_,_,_⟩
  · exact hzero.1
  · have hwh:w<tr.height 0:=by omega
    have hlen:(p.sched.map instOf).length≤33:=by simpa only [List.length_map] using prepD0_len hp
    have hns:∀P0∈p.sched.map instOf,1≤P0.n ∧ P0.n≤64:=by
      intro P0 hP
      obtain ⟨sp,hsp,rfl⟩:=List.mem_map.mp hP
      have hs:=prepD0_sched hp sp hsp
      exact ⟨hs.n1,hs.n64⟩
    have hqb:=ProcessRepairQueryAddress.query_address view hpar h68 I _ fwd hrec hlen hns hq hqa hqq
    have hwb:=ProcessRepairWriteAddress.write_address view hpar hpub67 hpub70 hpub72 hpub76 I hp fwd hrec hwh hwa hwq
    have hsame:cv (memory tr) 0 w tau=cv (memory tr) 0 q tau:=by
      unfold address at haddr
      omega
    exact (ProcessRepairWriteFrame.empty view hpub67 hpub75 hf hfs hff hc w hwh hwa (hsame.trans hqt) hwq).elim
end ZkFormal.NearV3.Candidates.ProcessRepairEmptyPriorRead
