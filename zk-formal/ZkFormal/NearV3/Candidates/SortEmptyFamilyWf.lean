import ZkFormal.NearV3.Candidates.SortEmptyShape
import ZkFormal.NearV3.Candidates.ProcPriorCodecCertifiedAdmission
namespace ZkFormal.NearV3.Candidates.SortEmptyFamily
open ZkFormal.Air ZkFormal.Size HorizontalProfile
open ProcPriorCodecActualFamily (fused)
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def rest : List Air.Table:=HorizontalAccounts.rest.set 10 SortEmpty.table
def tables : List Air.Table:=fused::rest.map InteractionTriples.table
def air : Air:=⟨tables,77,202⟩

theorem replaced_slot : tables[11]?=some (InteractionTriples.table SortEmpty.table) := by rfl

theorem wf_context (T : Air.Table) (d : Nat) :
    T.wf air d=T.wf ProcPriorCodecActualFamily.air d := rfl

theorem sort_wf : (InteractionTriples.table SortEmpty.table).wf air 16=true := by
  change (InteractionTriples.table SortEmpty.table).wf ⟨[],77,202⟩ 16=true
  decide +kernel

theorem tables_wf : tables.all (fun T=>T.wf air 16)=true := by
  change (fused::rest.map InteractionTriples.table).all _=true
  rw [List.all_cons,Bool.and_eq_true]
  constructor
  · rw [wf_context]
    exact ProcPriorCodecActualFamily.fused_wf
  · apply List.all_eq_true.mpr
    intro T hT
    obtain ⟨U,hU,rfl⟩:=List.mem_map.mp hT
    rcases List.mem_or_eq_of_mem_set hU with hU|rfl
    · rw [wf_context]
      exact List.all_eq_true.mp ProcPriorCodecActualFamily.rest_wf _ (List.mem_map.mpr ⟨U,hU,rfl⟩)
    · exact sort_wf


end ZkFormal.NearV3.Candidates.SortEmptyFamily
