import ZkFormal.NearV3.Candidates.ProcDistCmpInventory
import ZkFormal.NearV3.Candidates.ProcCodecConcatTraffic
namespace ZkFormal.NearV3.Candidates.ProcDistCmpTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete

def messages (row:Nat→Fp) : List (List Fp) :=
  List.replicate (if row Dist.cg=1 then 1 else 0) [row Dist.cx,row Dist.cy,row Dist.cb]

theorem row_messages (tr:Trace Fp)(t r:Nat)(pub:List Fp) :
    rowTraffic ScanDist.table.interactions tr t r pub B_SCMP true=messages (tr.cell t r) := by
  simp [ScanDist.table,ScanDist.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,messages,
    B_SPAR,B_SINC,B_SPUSH,B_SOP,B_SFIN,B_SCMP,B_SDLX,B_SDG]

theorem row_receives (tr:Trace Fp)(t r:Nat)(pub:List Fp) :
    rowTraffic ScanDist.table.interactions tr t r pub B_SCMP false=[] := by
  simp [ScanDist.table,ScanDist.interactions,rowTraffic,B_SPAR,B_SINC,B_SPUSH,B_SOP,B_SFIN,B_SCMP,B_SDLX,B_SDG]

theorem natural (row:Array Nat) : messages (fun c=>Fp.ofNat row[c]!)=
    (ProcDistCmpInventory.packet row).map cmpMsg := by
  simp [messages,ProcDistCmpInventory.packet,cmpMsg,List.map_replicate]

theorem generated (I:Input)(R:Run)(d:DistOut)(h:distRows I R=.ok d) :
    d.rows.toList.flatMap (fun row=>messages (fun c=>Fp.ofNat row[c]!))=d.cmps.map cmpMsg := by
  simp only [natural,←List.map_flatMap]
  exact congrArg (List.map cmpMsg) (ProcDistCmpInventory.generated I R d h)
end ZkFormal.NearV3.Candidates.ProcDistCmpTraffic
