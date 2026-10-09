import ZkFormal.NearV3.Candidates.ProcPriorCodecActual
import ZkFormal.NearV3.Candidates.ProcPriorTripleFusion
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecActualFamily
open ZkFormal.Air

/-- Only the four fields still used by Codec link initialization are exchanged. -/
def gridInteraction (i : Interaction) : Interaction:=
  if i.bus=Sched.B_SDG then {i with msg:=i.msg.take 4} else i

def routingBase : Air.Table:=ProcPriorFourStageLinearFusion.selected[9]!
def routing : Air.Table:={routingBase with interactions:=routingBase.interactions.map gridInteraction}

def components : List Air.Table:=ProcPriorVertical4Linear.components.set 2
  (ProcPriorRawFrame.table Sched.B_SPOST 73 B_VBYTES 74 75)
def overlay : Air.Table:=
  {ProcPriorVertical4Linear.table with
    constraints:=ProcPriorVertical4Linear.windows++
      components.zipIdx.flatMap (fun (T,i)=>(ProcPriorVertical4Linear.component i T).constraints),
    interactions:=components.zipIdx.flatMap (fun (T,i)=>(ProcPriorVertical4Linear.component i T).interactions)}

def selected : List Air.Table:=
  ((ProcPriorFourStageLinearFusion.selected.set 8 ProcPriorCodecActual.table).set 9 routing).set 19 overlay
def raw : Air.Table:=HorizontalTables.fuse selected
def paired : Air.Table:={raw with interactions:=InteractionPairing.reorder raw.interactions}
def tables : List Air.Table:=(paired::HorizontalAccounts.rest).map InteractionTriples.table
def air : Air:=⟨tables,77,202⟩
def bytes : Nat:=ZkFormal.Size.sizeOfWeq (ZkFormal.V2.G.pg 3) (tables.map (ZkFormal.Size.shapeOf 3))

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem routing_width : routingBase.width=119 := by decide +kernel
end ZkFormal.NearV3.Candidates.ProcPriorCodecActualFamily
