import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Tables
import ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair
import ZkFormal.NearV3.Assembly.RoutingQCandidate
import ZkFormal.NearV3.Render.Ups.CompactTableCandidate
import ZkFormal.NearV3.Render.Ups.CodecRelayCandidate
import ZkFormal.NearV3.Rcpt.Budget
import ZkFormal.Size.V3Synth
import ZkFormal.NearV3.Candidates.MerklePublic

/-! Concrete candidate inventory for measurement, NOT a complete admitted AIR.
Four SHA bins currently have capacity proofs only for source/upsert/sanity jobs;
all other SHA families still need placement in this same inventory. -/
namespace ZkFormal.NearV3.Candidates.CurrentFamily
open ZkFormal.Air ZkFormal.Size ZkFormal.Near
open Rcpt.Candidates

def shaTables : List Air.Table := List.replicate 4 (ZkFormal.Sha.Table.table B_BYTES B_DIGEST)

def trieTables : List Air.Table :=
  [SizeCount.nodeTable,HeadV3.table,SizeCount.valTable,WalkV3.table,Uniq.table,
    Render.UpsRelay.compactTable]

/-- Actual scheduler bus wiring, not the stand-in IDs used by the old shape model. -/
def chachaTables : List Air.Table :=
  [ZkFormal.Chacha.Table.table Sched.B_SCHACHA,
    ZkFormal.Chacha.Rng.Table.table Sched.B_SCHACHA Sched.B_SGEN,
    ZkFormal.Chacha.Shuffle.Table.table Sched.B_SSIN Sched.B_SSOUT Sched.B_SSMEM Sched.B_SGEN Sched.B_SSHUF]

def schedulerTables : List Air.Table :=
  [Render.UpsRelay.codecTable,Sched.ScanDist.table,Sched.Proc.table,Sched.Mem.table,Sched.Cmp.table Sched.B_SCMP]

def receiptTables : List Air.Table :=
  [Assembly.RoutingQCandidate.candidateTable,AcctV3.table,AkeyV3.table,BndV3.table] ++
    SourceLog22.tables ++ [SizeCount.sizeTable]

def merkleSortTables : List Air.Table :=
  [MerklePublic.table,{ZkFormal.Near.Sort.table with maxLog:=18}]

def tables : List Air.Table := shaTables ++ trieTables ++ chachaTables ++ schedulerTables ++
  receiptTables ++ merkleSortTables ++ [Qv.Candidates.KeyTrafficRepair.table]

def names : List String :=
  ["sha0","sha1","sha2","sha3","node-size-count","head","value-size-count","walk","uniq","compact-ups",
    "chacha","rng","shuffle","codec-relay","scan-dist","process","memory","compare",
    "receipt-q","account","account-key","boundary","source0","source1","source2","source3","size-count",
    "merkle","sort","queue-key-repair"]

def air : Air := ⟨tables,67,202⟩
def shapes (g : Nat) : List TShape := tables.map (shapeOf g)
def bytes (g : Nat) : Nat := sizeOfWeq (ZkFormal.V2.G.pg g) (shapes g)

set_option maxRecDepth 32768 in
theorem inventory_length : tables.length=30 ∧ names.length=tables.length := by decide +kernel

theorem actual_model (g : Nat) : ZkFormal.Size.sizeMaxDedup air (ZkFormal.V2.G.pg g)=bytes g :=
  sizeMaxDedup_eq_model air (ZkFormal.V2.G.pg g)
end ZkFormal.NearV3.Candidates.CurrentFamily
