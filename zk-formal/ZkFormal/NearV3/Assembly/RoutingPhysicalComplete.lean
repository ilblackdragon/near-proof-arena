import ZkFormal.NearV3.Assembly.RoutingPhysicalBalance

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3
open RoutingBoundedLayout

theorem physical_boundary_bus_balance (tr : Trace Fp) (t : Nat) (es : List BndE)
    (hn : (es.map BndE.rec4).Nodup)
    (hc : ∀r∈physicalActiveRows tr t,physicalBoundaryKey tr t r∈es.map BndE.rec4)
    (hu : ∀e∈es,e.U=physicalBoundaryUsers tr t e.rec4)
    (provider : Trace Fp) (pt : Nat) (pub : List Fp)
    (hp : TableTraffic BndV3.interactions provider pt pub (bndTraffic es)) :
    ∀msg,
      tableBusCount BndV3.interactions provider pt pub B_BND true msg+
        tableBusCount RcptV3.interactions (counterPatch tr t (physicalBoundaryRank tr t)) t pub B_BND true msg=
      tableBusCount RcptV3.interactions (counterPatch tr t (physicalBoundaryRank tr t)) t pub B_BND false msg+
        tableBusCount BndV3.interactions provider pt pub B_BND false msg := by
  intro msg
  rw [(hp B_BND msg).1,(hp B_BND msg).2,physical_counter_count,physical_counter_count]
  have h := ((physical_counter_balance tr t es hn hc hu).map Msg.toFp).count_eq msg
  simpa only [bndTraffic,bndSends,bndRecvs,if_pos rfl,ite_true,
    if_neg (show B_BND≠B_BNDP by decide),List.map_append,List.count_append] using h

/-- Concrete normalized BND provider plus counter-patched receipt trace.
Coverage of physical request keys by public records is the only bus ownership
premise; heights, usage counters, local legality and exact counter balance are
constructed. Installation at distinct slots of the final global trace is left
to the global table assembler. -/
theorem normalized_physical_complete {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint}
    {p : NearSpecV3.Prep} {k : NearSpecV3.WalkD0}
    (hp : NearSpecV3.prepD0 cb hint=.ok p) (hk : NearSpecV3.walkD0 cb=.ok k)
    {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : TableLocal candidateTable tr t pub)
    (hc : ∀r∈physicalActiveRows tr t,physicalBoundaryKey tr t r∈
      Public.boundaryRecords (boundedPrep p k.L k.H.shardId)) :
    let bounds := (boundedPrep p k.L k.H.shardId).bnds
    let es := boundaryEntries bounds (physicalBoundaryKeys tr t)
    let provider := boundaryTrace bounds (physicalBoundaryKeys tr t)
    TableLocal candidateTable (counterPatch tr t (physicalBoundaryRank tr t)) t pub ∧
    TableLocal BndV3.table provider 0 pub ∧
    TableTraffic BndV3.interactions provider 0 pub (bndTraffic es) ∧
    ∀msg,
      tableBusCount BndV3.interactions provider 0 pub B_BND true msg+
        tableBusCount RcptV3.interactions (counterPatch tr t (physicalBoundaryRank tr t)) t pub B_BND true msg=
      tableBusCount RcptV3.interactions (counterPatch tr t (physicalBoundaryRank tr t)) t pub B_BND false msg+
        tableBusCount BndV3.interactions provider 0 pub B_BND false msg := by
  dsimp only
  obtain ⟨hw,he,hl,ht⟩ := physical_provider_render hp hk hL
  refine ⟨ranked_trace_local hL,hl,ht,?_⟩
  apply physical_boundary_bus_balance tr t _ (boundaryEntries_nodup _ _) ?_
    (physicalEntries_usage_all _ tr t) _ 0 pub ht
  intro r hr
  rw [he]
  exact hc r hr

end ZkFormal.NearV3.Assembly.RoutingQCandidate
