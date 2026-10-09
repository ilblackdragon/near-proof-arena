import ZkFormal.NearV3.Candidates.ProcPriorVertical4Linear
import ZkFormal.NearV3.Candidates.ProcPriorCodecParameter
import ZkFormal.NearV3.Rcpt.Candidates.EmptyValueFusion
namespace ZkFormal.NearV3.Candidates.ProcPriorFourStageLinearFusion
open ZkFormal.Air

def selected : List Air.Table:=
  (Rcpt.Candidates.EmptyValueFusion.selected.set 8 ProcPriorCodecParameter.table).set 19 ProcPriorVertical4Linear.table

def raw : Air.Table:=HorizontalTables.fuse selected
def table : Air.Table:={raw with interactions:=InteractionPairing.reorder raw.interactions}
def tables : List Air.Table:=table::HorizontalAccounts.rest
def bytes : Nat:=ZkFormal.Size.sizeOfWeq (ZkFormal.V2.G.pg 2) (tables.map (ZkFormal.Size.shapeOf 2))

theorem codec_slot : Rcpt.Candidates.EmptyValueFusion.selected[8]?=some Render.UpsRelay.codecTable := rfl
theorem overlay_slot : Rcpt.Candidates.EmptyValueFusion.selected[19]?=some ProcPriorVertical.table := rfl

end ZkFormal.NearV3.Candidates.ProcPriorFourStageLinearFusion
