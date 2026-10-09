import ZkFormal.NearV3.Candidates.ProcPriorRoutedWriteStamp
import ZkFormal.NearV3.Candidates.ProcPriorRoutedPreparedQuery
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedAddressResidual
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)

/-- Query addresses and all write stamps are authenticated internally. Only
WRITE addresses remain as a range obligation for the global memory order. -/
theorem consumer {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpar:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h68:∀seg∈AP.pubSegs,seg.bus≠68)
    (h67:∀msg,pubCount AP pub 67 true msg=0)
    (h40:∀seg∈AP.pubSegs,seg.bus≠40)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    (hwrite:∀r,r<tr.height 0→Live (memory tr) 0 r→cv (memory tr) 0 r query=0→address (memory tr) 0 r<2^29)
    {tc r:Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i:Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hib:i.bus=68) (his:i.send=false)
    (him:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧ Live (memory tr) 0 q ∧ cv (memory tr) 0 q query=1 ∧
      ProcPriorVerticalReadSound.read.msgVal (memory tr) 0 q pub=i.msgVal tr tc r pub ∧
      Result (memory tr) 0 q := by
  have hL:=ProcPriorRoutedMemoryOrder.local_memory hH htables
  have haddr:∀r,r<tr.height 0→Live (memory tr) 0 r→address (memory tr) 0 r<2^29 := by
    intro q hq ha
    have hb:=ProcPriorMemorySoundRows.flag (live_local hL hq ha) (x:=query) (by simp)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hz|hz
    · exact hwrite q hq ha hz
    · exact (ProcPriorRoutedPreparedQuery.query_address hH htables hpar h68 I hprep fwd hrec hq ha hz).2.2
  have hstamp:∀r,r<tr.height 0→Live (memory tr) 0 r→cv (memory tr) 0 r query=0→cv (memory tr) 0 r stamp+1<2^29 := by
    intro q hq ha hz
    exact ProcPriorRoutedWriteStamp.write_stamp hH htables h67 hq ha hz
  have hp68:∀msg,pubCount AP pub 68 true msg=0 := by
    intro msg
    exact pubCount_zero (fun seg hseg hbus=>absurd hbus (h68 seg hseg)) msg
  exact ProcPriorRoutedLastWrite.consumer hH htables hp68 h40 haddr hstamp ht hr hi hib his him
end ZkFormal.NearV3.Candidates.ProcPriorRoutedAddressResidual
