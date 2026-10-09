import ZkFormal.NearV3.Candidates.ProcPriorRoutedQueryAddress
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedPreparedQuery
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)

/-- Accepted preparation supplies the instance-count and shard-count bounds;
only the authentic public SPAR inventory and public bus ownership are exposed. -/
theorem query_address {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h68:∀seg∈AP.pubSegs,seg.bus≠68)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {r:Nat} (hr:r<tr.height 0) (ha:Live (memory tr) 0 r)
    (hq:cv (memory tr) 0 r query=1) :
    cv (memory tr) 0 r tau<33 ∧ cv (memory tr) 0 r link<4096 ∧ address (memory tr) 0 r<2^29 := by
  have hl:(p.sched.map instOf).length≤33 := by
    rw [List.length_map]
    exact prepD0_len hprep
  have hn:∀P0∈p.sched.map instOf,1≤P0.n ∧ P0.n≤64 := by
    intro P0 hm
    obtain ⟨sp,hsp,he⟩:=List.mem_map.mp hm
    subst P0
    have hs:=prepD0_sched hprep sp hsp
    exact ⟨hs.n1,hs.n64⟩
  exact ProcPriorRoutedQueryAddress.query_address hH htables hpub h68 I _ fwd hrec hl hn hr ha hq
end ZkFormal.NearV3.Candidates.ProcPriorRoutedPreparedQuery
