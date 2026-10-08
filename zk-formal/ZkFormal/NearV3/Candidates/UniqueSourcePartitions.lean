import ZkFormal.NearV3.Candidates.UniqueSourceRender
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Tables
namespace ZkFormal.NearV3.Candidates.UniqueSourcePartitions
set_option maxRecDepth 32768
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl Rcpt.Candidates
open DedupPartitionTable

def rightBase : List Expr := UniqueSourceCharge.constraints.mapIdx fun i e=>
  if i∈[14,15,16,51] then k 0 else e

def first : Air.Table := { SourceLog22.firstTable with
  constraints:=UniqueSourceCharge.constraints.map fun e=>.mul (not .isLast) e }

def middle (incoming outgoing : Nat) : Air.Table := {SourceLog22.middleTable incoming outgoing with
  constraints:=rightBase.map fun e=>.mul (not .isLast) e }

def last : Air.Table := {SourceLog22.lastTable with constraints:=rightBase++[rightEndpoint]}

def tables : List Air.Table := [first,middle 64 65,middle 65 66,last].map SizeCount.sourceTable

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem shapes : tables.map (ZkFormal.Size.shapeOf 2)=SourceLog22.tables.map (ZkFormal.Size.shapeOf 2) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem wellformed : tables.all (Air.Table.wf ⟨tables,67,202⟩ 6)=true := by decide +kernel

theorem interactions : tables.map Air.Table.interactions=SourceLog22.tables.map Air.Table.interactions := rfl

theorem height_cap : ∀T∈tables,T.maxLog=22 := by decide +kernel
end ZkFormal.NearV3.Candidates.UniqueSourcePartitions
