import ZkFormal.NearV3.Candidates.ProcPriorRoutedWriteAddress
import ZkFormal.NearV3.Candidates.ProcPriorRoutedAddressResidual
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedAuthenticatedRead
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)

/-- Corrected prior-read last-write extraction from the actual installed
routed family, with every comparator address/stamp range authenticated.
Public input ownership/inventory remains explicit; no generated trace,
caller-supplied range/order or standalone component ownership is assumed. -/
theorem consumer {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpar:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h68:∀seg∈AP.pubSegs,seg.bus≠68) (h40:∀seg∈AP.pubSegs,seg.bus≠40)
    (h67:∀msg,pubCount AP pub 67 true msg=0)
    (h70:∀msg,pubCount AP pub 70 true msg=0)
    (h72:∀msg,pubCount AP pub 72 true msg=0)
    (h76:∀msg,pubCount AP pub 76 true msg=0)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {tc r:Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i:Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hib:i.bus=68) (his:i.send=false)
    (him:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧ Live (memory tr) 0 q ∧ cv (memory tr) 0 q query=1 ∧
      ProcPriorVerticalReadSound.read.msgVal (memory tr) 0 q pub=i.msgVal tr tc r pub ∧
      Result (memory tr) 0 q := by
  apply ProcPriorRoutedAddressResidual.consumer hH htables hpar h68 h67 h40 I hp fwd hrec
    (fun q hq ha hquery=>(ProcPriorRoutedWriteAddress.write_address hH htables hpar h67 h70 h72 h76 I hp fwd hrec hq ha hquery).2.2)
    ht hr hi hib his him
end ZkFormal.NearV3.Candidates.ProcPriorRoutedAuthenticatedRead
