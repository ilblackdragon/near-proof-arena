import ZkFormal.NearV3.Rcpt.Candidates.SizeCountDecorate

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl

/-- Uniform source extension preserves the complete source traffic and appends
zero native store records, including partitioned source tables. -/
theorem source_size_traffic (T : ZkFormal.Air.Table) (tr : Trace Fp)
    (t : Nat) (pub : List Fp) (rows : List Nat) :
    rows.flatMap (fun r => rowTraffic (sourceTable T).interactions tr t r pub B_SIZE true)=
      (rows.flatMap (fun r => rowTraffic T.interactions tr t r pub B_SIZE true)).map
        (fun msg => msg++[0]) := by
  simp only [sourceTable,rowTraffic_withCount,ite_true,eval_k,List.map_flatMap]
  rfl

theorem source_size_sender (T : ZkFormal.Air.Table) (tr : Trace Fp)
    (t : Nat) (pub : List Fp) (n : Nat)
    (hs : (List.range (tr.height t)).flatMap
      (fun r => rowTraffic T.interactions tr t r pub B_SIZE true)=[[2,(n:Fp)]]) :
    (List.range (tr.height t)).flatMap
      (fun r => rowTraffic (sourceTable T).interactions tr t r pub B_SIZE true)=[[2,(n:Fp),0]] := by
  rw [source_size_traffic,hs]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
