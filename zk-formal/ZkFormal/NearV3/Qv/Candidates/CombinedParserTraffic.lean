import ZkFormal.NearV3.Qv.Candidates.CombinedParser
import ZkFormal.NearV3.Qv.Candidates.CombinedLocal
import ZkFormal.NearV3.Qv.Candidates.RecordTrafficContract

namespace ZkFormal.NearV3.Qv.Candidates.CombinedTable
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

/-- Parser rows preserve the original provider/byte/shard traffic and are silent
on walk-only interactions. -/
theorem parser_row_traffic_zero (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hz : ∀ x,37≤x → tr.cell t r x=0) (bus : Nat) (sd : Bool) :
    rowTraffic interactions tr t r pub bus sd=
      rowTraffic ValueTable.interactions tr t r pub bus sd := by
  exact parser_row_traffic tr t r pub (hz _ (by decide)) (hz _ (by decide))
    (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) bus sd

end ZkFormal.NearV3.Qv.Candidates.CombinedTable

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ValueGen

theorem mixedTrace_parser_row_traffic (ws : List Walk) (vs : List Record)
    (log j : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) :
    rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0
      ((ws.flatMap Walk.rows).length+j) pub bus sd=
      (natRowTraffic ValueTable.interactions ((recordsRows vs).getD j []) bus sd).map Msg.toFp := by
  rw [CombinedTable.parser_row_traffic_zero _ _ _ _ (fun x hx => by
    rw [mixedTrace_suffix]; exact recordsCell_high vs j x hx)]
  apply rowTraffic_nat _ _ _ _ _ _ (fun c => by rw [mixedTrace_suffix]; rfl)
  intro i hi
  have h := List.all_eq_true.mp interaction_nat_fragment i hi
  simp only [Bool.and_eq_true] at h
  exact ⟨fun b hb => ⟨List.all_eq_true.mp h.1 b hb,records_nat_bits vs j i hi b hb⟩,
    fun e he => List.all_eq_true.mp h.2 e he⟩

/-- The whole physical suffix, including padding, emits exactly standalone
parser traffic. No assumptions about provider ownership or bus balance. -/
theorem mixedTrace_parser_suffix_traffic (ws : List Walk) (vs : List Record)
    (log : Nat) (pub : List Fp) (bus : Nat) (sd : Bool)
    (hfit : (ws.flatMap Walk.rows).length+(recordsRows vs).length≤2^log) :
    (List.range (2^log-(ws.flatMap Walk.rows).length)).flatMap (fun j =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0
        ((ws.flatMap Walk.rows).length+j) pub bus sd)=
      ((recordsRows vs).flatMap (fun row => natRowTraffic ValueTable.interactions row bus sd)).map Msg.toFp := by
  simp only [mixedTrace_parser_row_traffic]
  rw [← List.map_flatMap,flatMap_getD_padded [] (recordsRows vs)
    (fun row => natRowTraffic ValueTable.interactions row bus sd)
    (natRowTraffic_zero bus sd) _ (by omega)]

theorem mixedTrace_parser_suffix_canonical (ws : List Walk) (vs : List Record)
    (hv : ∀ v ∈ vs,v.Valid) (log : Nat) (pub : List Fp) (bus : Nat) (sd : Bool)
    (hfit : (ws.flatMap Walk.rows).length+recordsSize vs≤2^log) :
    ((List.range (2^log-(ws.flatMap Walk.rows).length)).flatMap (fun j =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0
        ((ws.flatMap Walk.rows).length+j) pub bus sd)).Perm
      ((if sd then (canonicalTraffic vs).sends bus else (canonicalTraffic vs).recvs bus).map Msg.toFp) := by
  rw [mixedTrace_parser_suffix_traffic ws vs log pub bus sd (by rw [recordsRows_length vs hv]; exact hfit)]
  have h := recordsTraffic_canonical vs hv bus
  cases sd
  · exact h.2.map Msg.toFp
  · exact h.1.map Msg.toFp

/-- Exact accounting of all physical rows, separating the walk prefix from the
canonical parser contribution without dropping or duplicating any messages. -/
theorem mixedTrace_traffic_split (ws : List Walk) (vs : List Record)
    (hv : ∀ v ∈ vs,v.Valid) (log : Nat) (pub : List Fp) (bus : Nat) (sd : Bool)
    (hfit : (ws.flatMap Walk.rows).length+recordsSize vs≤2^log) :
    ((List.range (2^log)).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub bus sd)).Perm
      (((List.range (ws.flatMap Walk.rows).length).flatMap (fun r =>
        rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub bus sd)) ++
       (if sd then (canonicalTraffic vs).sends bus else (canonicalTraffic vs).recvs bus).map Msg.toFp) := by
  have he : 2^log=(ws.flatMap Walk.rows).length+(2^log-(ws.flatMap Walk.rows).length) := by omega
  have hrange := congrArg List.range he
  rw [List.range_add] at hrange
  rw [hrange,List.flatMap_append,List.flatMap_map]
  exact (mixedTrace_parser_suffix_canonical ws vs hv log pub bus sd hfit).append_left _

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
