import ZkFormal.NearV3.Candidates.ProcPriorFourStageLinearFusion
import ZkFormal.NearV3.Candidates.InteractionTriples
namespace ZkFormal.NearV3.Candidates.ProcPriorTripleFusion
open ZkFormal.Air

def tables : List Air.Table:=ProcPriorFourStageLinearFusion.tables.map InteractionTriples.table
def air : Air:=⟨tables,77,202⟩
def bytes : Nat:=ZkFormal.Size.sizeOfWeq (ZkFormal.V2.G.pg 3) (tables.map (ZkFormal.Size.shapeOf 3))

end ZkFormal.NearV3.Candidates.ProcPriorTripleFusion
