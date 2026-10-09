import ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedDegree
import ZkFormal.NearV3.Candidates.InteractionTriplesWf
namespace ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedFamily
open ZkFormal.Air HorizontalProfile
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem selected_wf : ProcPriorProcessRepairedFamily.selected.all (fun T=>T.wf air 16)=true := by
  decide +kernel

theorem fused_wf : fused.wf air 16=true := by
  apply InteractionTriples.wf _ _ _ (by decide)
  rw [ProcPriorProcessRepairedFamily.paired,InteractionPairing.wf]
  exact HorizontalWf.fuse_wf air ProcPriorProcessRepairedFamily.selected 16
    (List.all_eq_true.mp selected_wf)

theorem rest_wf : (HorizontalAccounts.rest.map InteractionTriples.table).all (fun T=>T.wf air 16)=true := by
  decide +kernel

theorem tables_wf : air.tables.all (fun T=>T.wf air 16)=true := by
  change (fused::HorizontalAccounts.rest.map InteractionTriples.table).all _=true
  rw [List.all_cons,fused_wf,rest_wf]
  rfl
end ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedFamily
