import ZkFormal.NearV3.Qv.Candidates.CombinedTraffic
import ZkFormal.NearV3.Qv.Candidates.CombinedPublic

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec ValueGen

/-- The honest mixed renderer binds its implicit count to the actual prepared
public header bytes. Native assembly supplies the matching trace length. -/
theorem plan_prepared_local_and_traffic (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (resolve : Resolve) (hv : v.Valid) (d : Walk) (vs : List Record)
    (hvs : ∀ v ∈ vs,v.Valid) (log : Nat) (p : NearSpecV3.Prep) (overhead : Nat)
    (hlog : 1≤log ∧ log≤CombinedTable.table.maxLog)
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length+recordsSize vs≤2^log)
    (hroots : Public.RootsSized p) (hK : p.hdr.K<256^4) (hcount : pres.length=p.hdr.K) :
    let pub := ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)
    TableLocal CombinedTable.table (mixedTrace (plan pre v pres resolve) vs log) 0 pub ∧
    TableTraffic CombinedTable.interactions (mixedTrace (plan pre v pres resolve) vs log) 0 pub
      (mixedTraffic (plan pre v pres resolve) vs) := by
  apply plan_local_and_traffic pre v pres resolve hv d vs hvs log _ hlog hfit
  intro r
  rw [CombinedTable.kPublic_prepared _ _ _ p overhead hroots hK,hcount,natCast_eq]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
