import ZkFormal.NearV3.Candidates.ProcessRepairBoundedLastWrite
import ZkFormal.NearV3.Candidates.ProcessRepairQueryAddress
import ZkFormal.NearV3.Candidates.ProcPriorPublicSenderBound
namespace ZkFormal.NearV3.Candidates.ProcessRepairPreparedLastWrite
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
    (hwrite:∀r,r<tr.height 0→Live (memory tr) 0 r→cv (memory tr) 0 r query=0→address (memory tr) 0 r<2^29)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hib:i.bus=68) (his:i.send=false)
    (him:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧ Live (memory tr) 0 q ∧ cv (memory tr) 0 q query=1 ∧
      ProcPriorVerticalReadSound.read.msgVal (memory tr) 0 q pub=i.msgVal tr tc r pub ∧
      Result (memory tr) 0 q := by
  have hlen:(p.sched.map instOf).length≤33:=by simpa only [List.length_map] using prepD0_len hp
  have hns:∀P0∈p.sched.map instOf,1≤P0.n ∧ P0.n≤64:=by
    intro P0 hP
    obtain ⟨sp,hsp,rfl⟩:=List.mem_map.mp hP
    have hs:=prepD0_sched hp sp hsp
    exact ⟨hs.n1,hs.n64⟩
  have haddr:∀r,r<tr.height 0→Live (memory tr) 0 r→address (memory tr) 0 r<2^29:=by
    intro r hr ha
    have hL:=ProcessRepairMemoryOrder.local_memory view
    have hl:=live_local hL hr ha
    have hq:=ProcPriorMemorySoundRows.flag hl (x:=query) (by simp)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with hq|hq
    · exact hwrite r hr ha hq
    · exact (ProcessRepairQueryAddress.query_address view hpar h68 I _ fwd hrec hlen hns hr ha hq).2.2
  exact ProcessRepairBoundedLastWrite.consumer view hpub67 hpub68 hpub40 haddr ht hr hi hib his him
end ZkFormal.NearV3.Candidates.ProcessRepairPreparedLastWrite
