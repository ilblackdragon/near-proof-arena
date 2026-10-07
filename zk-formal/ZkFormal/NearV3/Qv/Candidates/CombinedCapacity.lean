import ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
import ZkFormal.NearV3.Qv.Candidates.RecordTraffic

/-! Honest row arithmetic. Assembly must supply the actual ownership and byte
budgets; this theorem does not impose additional native acceptance conditions. -/
namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open NearSpec

theorem plan_rows_bound (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (hv : v.Valid) (hb : (v.buffered.map List.length).getD 0 ≤ 3000000)
    (hK : pres.length ≤ 31) :
    ((plan pre v pres resolve).flatMap Walk.rows).length ≤ 1125034 := by
  have hn := main_group_count_bound v hv hb
  rw [plan_rows_length]
  omega

theorem combined_rows_fit (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (hv : v.Valid) (hb : (v.buffered.map List.length).getD 0 ≤ 3000000)
    (hK : pres.length ≤ 31) (vs : List ValueGen.Record)
    (hvs : ∀ x ∈ vs, x.Valid)
    (hbytes : (vs.map fun x => x.bytes.length).sum ≤ 2^21)
    (hrecords : vs.length ≤ 134028) :
    ((plan pre v pres resolve).flatMap Walk.rows).length + ValueGen.recordsSize vs ≤ 2^22 := by
  have hw := plan_rows_bound pre v pres resolve hv hb hK
  have hp := ValueGen.recordsSize_le vs hvs
  have h2 : 2^21 = 2097152 := by decide
  have h4 : 2^22 = 4194304 := by decide
  rw [h2] at hbytes
  rw [h4]
  omega

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
