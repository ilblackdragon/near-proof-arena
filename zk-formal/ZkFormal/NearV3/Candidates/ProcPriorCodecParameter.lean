import ZkFormal.NearV3.Render.Ups.CodecRelayCandidate
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecParameter
open ZkFormal.Air ZkFormal.Chacha.Table.E

def interaction : Interaction:=
  {bus:=76,send:=true,mult:=[c Sched.Codec.kF],msg:=[c Sched.Codec.tau,c Sched.Codec.nn]}

def table : Air.Table:=
  {Render.UpsRelay.codecTable with interactions:=Render.UpsRelay.codecTable.interactions++[interaction]}

theorem width : table.width=Render.UpsRelay.codecTable.width := rfl
theorem constraints : table.constraints=Render.UpsRelay.codecTable.constraints := rfl

end ZkFormal.NearV3.Candidates.ProcPriorCodecParameter
