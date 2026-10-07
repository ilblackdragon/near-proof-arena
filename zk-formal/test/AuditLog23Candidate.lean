import ZkFormal.V2.Log23.Budget
import ZkFormal.V2.Log23.Verifier
import ZkFormal.V2.Log23.TransportBudget
import ZkFormal.V2.Log23.QueryBound

/-- info: 'ZkFormal.V2.Log23.tableWf_22' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.tableWf_22
/-- info: 'ZkFormal.V2.Log23.airWf_22' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.airWf_22
/-- info: 'ZkFormal.V2.Log23.publicWf_22' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.publicWf_22
/-- info: 'ZkFormal.V2.Log23.tableWf_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.tableWf_mono
/-- info: 'ZkFormal.V2.Log23.tableWf_facts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.tableWf_facts
/-- info: 'ZkFormal.V2.Log23.publicWf_air' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.publicWf_air
/-- info: 'ZkFormal.V2.Log23.headerOk_facts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.headerOk_facts
/-- info: 'ZkFormal.V2.Log23.header_log_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.header_log_bounds
#print axioms ZkFormal.V2.Log23.query_bit_budget
#print axioms ZkFormal.V2.Log23.unchanged_proof_cap
/-- info: 'ZkFormal.V2.Log23.layout_lde_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.layout_lde_bound
/-- info: 'ZkFormal.V2.Log23.queryLog_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.queryLog_bound
#print axioms ZkFormal.V2.Log23.numerical_security_128
#print axioms ZkFormal.V2.Log23.numerical_security_margin_132
#print axioms ZkFormal.V2.Log23.numerical_207_queries_insufficient
/-- info: 'ZkFormal.V2.Log23.coarse_fri_budget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.coarse_fri_budget
/-- info: 'ZkFormal.V2.Log23.verifierHeader_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.verifierHeader_bounds

namespace Log23Regression
open ZkFormal.Air ZkFormal.V2 ZkFormal.V2.Log23
def air (cap : Nat) : AirP :=
  { tables := [{ width := 1, constraints := [], interactions := [], maxLog := cap }],
    numBuses := 0, numPub := 0, pubSegs := [], maxPub := 0 }
example : verifierHeader (air 23) 2 [23] = true := by decide
example : (air 23).wf 16 = false := by decide
example : verifierHeader (air 24) 2 [24] = false := by decide
example : verifierHeader (air 23) 0 [23] = false := by decide
example : verifierHeader (air 23) 4 [23] = false := by decide
example : verifierHeader (air 23) 2 [3] = false := by decide
example : verifierHeader (air 23) 2 [4] = true := by decide
example : headerOk (air 23).toAir { params 2 with posBits := 26 } [23] = false := by decide
end Log23Regression

#print axioms ZkFormal.V2.Log23.dominates_through_27
/-- info: 'ZkFormal.V2.Log23.header_chunk_good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.header_chunk_good
#print axioms ZkFormal.V2.Log23.query_budget
/-- info: 'ZkFormal.V2.Log23.full_transport_budget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.full_transport_budget

/-- info: 'ZkFormal.V2.Log23.schedule_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.schedule_bound
/-- info: 'ZkFormal.V2.Log23.oracles_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.oracles_bound
/-- info: 'ZkFormal.V2.Log23.schedule_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.schedule_ok
/-- info: 'ZkFormal.V2.Log23.iop_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.iop_bounds
/-- info: 'ZkFormal.V2.Log23.verifier_query_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Log23.verifier_query_bound
