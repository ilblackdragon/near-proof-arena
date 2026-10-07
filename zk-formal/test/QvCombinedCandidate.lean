import ZkFormal.NearV3.Qv.Candidates.CombinedParser
import ZkFormal.NearV3.Qv.Candidates.CombinedPublic
import ZkFormal.NearV3.Qv.Candidates.ValueGen
import ZkFormal.NearV3.Qv.Candidates.CombinedCapacity
import ZkFormal.NearV3.Qv.Candidates.CombinedWalkBits
import ZkFormal.NearV3.Qv.Candidates.CombinedWalkTraffic
import ZkFormal.NearV3.Qv.Candidates.CombinedShardTraffic
import ZkFormal.NearV3.Qv.Candidates.CombinedWordTraffic
import ZkFormal.NearV3.Qv.Candidates.CombinedWalkBase
import ZkFormal.NearV3.Qv.Candidates.CombinedBoolean

namespace QvCombinedRegression
open ZkFormal.NearV3.Qv.Candidates

def walkRow (typ pos tau slot count byte : Nat) (first last finish finalMain : Bool)
    (vid : Nat := 0) (absent : Bool := true) : List Nat :=
  let isMain := tau == 0
  let mode := if isMain then (if typ=1 then 1 else if typ=3 then 2 else 0) else 2
  let base := (ValueGen.row ⟨vid,tau,0,2,0,count⟩ 0 0 4 0 0
    ((List.range 8).map fun i => UInt8.ofNat (byte / 2^i % 2))).set 4 mode
  let present := last && !absent
  base ++ [1,typ%2,typ/2,pos,byte,slot,first.toNat,last.toNat,finish.toNat,absent.toNat,
    (decide (typ=3) && !first).toNat,(present && isMain && decide (typ=1)).toNat,
    isMain.toNat,finalMain.toNat,present.toNat]

def allAbsent (K : Nat) : List (List Nat) :=
  [walkRow 0 0 0 0 0 7 true true false false,
   walkRow 1 0 0 1 0 13 true true false false,
   walkRow 2 0 0 2 0 10 true true (K==0) true] ++
  (List.range K).map (fun i => walkRow 0 0 (i+1) 0 0 7 true true (i+1==K) false)

def check (rows : List (List Nat)) (log K : Nat) : Bool :=
  let trace : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
    { log := fun _ => log, cell := fun _ r c => ZkFormal.Algebra.Fp.ofNat ((rows.getD r []).getD c 0) }
  let pub := List.replicate 26 (0 : ZkFormal.Algebra.Fp) ++
    (List.range 4).map (fun i => ZkFormal.Algebra.Fp.ofNat (K/256^i%256))
  rows.length ≤ 2^log && (List.range (2^log)).all fun r =>
    CombinedTable.table.allConstraints.all fun e => decide (e.eval trace 0 r pub=0)

#guard check (allAbsent 0) 2 0
#guard check (allAbsent 1) 2 1
#guard check (allAbsent 2) 3 2
#guard !(check (allAbsent 0) 2 1)
#guard !(check ((allAbsent 0).modify 1 (fun r => r.set 41 10)) 2 0)
#guard !(check ((allAbsent 0).modify 1 (fun r => r.set 42 2)) 2 0)
#guard !(check ((allAbsent 0).modify 2 (fun r => r.set 50 0)) 2 0)
#guard !(check ((allAbsent 0).modify 0 (fun r => r.set 4 2)) 2 0)
#guard !(check ((allAbsent 0).modify 0 (fun r => r.set 29 2)) 2 0)

-- One present delayed value, then an actual empty-index parser record.
def delayed : List (List Nat) :=
  ((allAbsent 0).set 0 (walkRow 0 0 0 0 0 7 true true false false 4 false)) ++
    ValueGen.emptyRows 4 0 1 (NearSpec.u64 300)
#guard check delayed 5 0

-- A buffered group-data read uses raw mode, matching native ReadPlan.mainRequests.
def grouped : List (List Nat) :=
  [walkRow 0 0 0 0 1 7 true true false false,
   walkRow 1 0 0 1 1 13 true true false false 5 false,
   walkRow 2 0 0 2 1 10 true true false false] ++
  (([16] ++ List.replicate 8 0).zipIdx.map fun (b,i) =>
    walkRow 3 i 0 3 1 b (i==0) (i==8) (i==8) true) ++
  ValueGen.bufferRows 5 0 1 [⟨NearSpec.u64 0,NearSpec.u64 42⟩]
#guard check grouped 6 0
#guard !(check (grouped.modify 3 (fun r => r.set 4 0)) 6 0)
end QvCombinedRegression

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.shape_g2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.shape_g2
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.table_wf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.table_wf

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.parserExpr_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.parserExpr_eval
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.parserEnv_eq' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.parserEnv_eq
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_row_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_row_preserved

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_constraint_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_constraint_mem
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_constraints_of_combined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_constraints_of_combined
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_flags_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_flags_zero
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_row_traffic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_row_traffic
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_traffic_of_combined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_traffic_of_combined

/-- info: 'ZkFormal.NearV3.Public.prep_tag_prefix_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.prep_tag_prefix_length
/-- info: 'ZkFormal.NearV3.Public.header_implicit_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.header_implicit_count
/-- info: 'ZkFormal.NearV3.Public.prepared_implicit_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.prepared_implicit_count
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.kPublic_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.kPublic_eval
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.kPublic_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.kPublic_prepared

namespace QvCombinedRegression
open ZkFormal.NearV3.Qv ZkFormal.NearV3.Qv.Candidates
open NearSpec

def noQueueKeys : PTrie := .leaf [] (.val []) 0

def nativeEmpty : MainValues := ⟨none,none,[],none⟩
#guard check ((CombinedWalkGen.plan noQueueKeys nativeEmpty [] (fun _ _ => (0,0))).flatMap
  CombinedWalkGen.Walk.rows) 2 0
#guard check ((CombinedWalkGen.plan noQueueKeys nativeEmpty [noQueueKeys,noQueueKeys] (fun _ _ => (0,0))).flatMap
  CombinedWalkGen.Walk.rows) 3 2

def nativeGroup : MainValues :=
  ⟨none,some (u32 1 ++ u64 0 ++ u64 42 ++ u64 42),[0],none⟩
#guard check (((CombinedWalkGen.plan noQueueKeys nativeGroup [] (fun _ _ => (5,0))).flatMap
  CombinedWalkGen.Walk.rows) ++ ValueGen.bufferRows 5 0 1 [⟨u64 0,u64 42⟩]) 6 0
end QvCombinedRegression

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.rows_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.rows_length
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.row_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.row_width
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.mainPlan_requests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.mainPlan_requests
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.implicitPlan_requests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.implicitPlan_requests
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.mainPlan_rows_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.mainPlan_rows_length
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.implicitPlan_rows_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.implicitPlan_rows_length
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.plan_rows_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.plan_rows_length
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.applyNewChunk_plan_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.applyNewChunk_plan_reads
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.plan_rows_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.plan_rows_bound
/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.combined_rows_fit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.combined_rows_fit

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.byte_low_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.byte_low_bits

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.byte_high_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.byte_high_bits

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.low_nibble' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.low_nibble

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.high_nibble' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.high_nibble

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.byte_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.byte_reconstructed

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.field_low_nibble' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.field_low_nibble

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.field_high_nibble' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.field_high_nibble

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_symbols' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_symbols

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.parser_silent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.parser_silent

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.key_traffic_filter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.key_traffic_filter

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_nat_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_nat_bits

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_field_traffic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_field_traffic

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_field_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_field_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.terminal_filter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.terminal_filter

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.terminal_nat_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.terminal_nat_bits

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.final_nat_messages' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.final_nat_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.counter_nat_messages' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.counter_nat_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.final_field_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.final_field_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.counter_field_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.counter_field_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.shard_field_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.shard_field_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.mainPlan_group_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.mainPlan_group_slot

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.implicitPlan_group_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.implicitPlan_group_slot

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.plan_group_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.plan_group_slot

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.final_word_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.final_word_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.counter_word_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.counter_word_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_word_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_word_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.shard_word_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.shard_word_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.final_word_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.final_word_field

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.counter_word_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.counter_word_field

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_word_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.key_word_field

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.shard_word_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.shard_word_field

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_row_preserved_or_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_row_preserved_or_zero

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_wrap_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedTable.parser_wrap_preserved

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.first_main_mode_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.first_main_mode_zero

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.generated_parser_wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.generated_parser_wrap

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.base_constraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.base_constraints

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.base_to_walk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.base_to_walk

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.base_to_padding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.base_to_padding

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.flag_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.flag_bounds

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.byte_bit_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.byte_bit_bounds

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.flag_constraints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.flag_constraints

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.byte_bit_constraints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.byte_bit_constraints

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.multiplicity_constraints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.multiplicity_constraints

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.table_bit_constraints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.table_bit_constraints

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.inactive_gate_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.Walk.inactive_gate_zero
