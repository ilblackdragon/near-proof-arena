import ZkFormal.NearV3.Qv.Candidates.CombinedOverlay
import ZkFormal.NearV3.Qv.Candidates.ValueGen

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
