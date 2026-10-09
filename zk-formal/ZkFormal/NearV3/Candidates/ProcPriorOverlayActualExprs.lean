import ZkFormal.NearV3.Assembly.SchedulerPriorActualOverlay
import ZkFormal.NearV3.Candidates.ProcPriorOverlayTrafficRanges
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayActualExprs
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorVertical4Linear ProcPriorCells

theorem exprs_eq : ProcPriorCodecActualFamily.components.flatMap Air.Table.exprs=
    components.flatMap Air.Table.exprs := rfl

theorem mults_eq : ProcPriorCodecActualFamily.components.flatMap
    (fun T=>T.interactions.flatMap Interaction.mult)=
    components.flatMap (fun T=>T.interactions.flatMap Interaction.mult) := rfl

theorem bounds (T : Air.Table) (hT:T∈ProcPriorCodecActualFamily.components)
    (e : Expr) (he:e∈T.exprs) : e.colBound≤23 ∧ e.pubBound=0 := by
  have hm:e∈ProcPriorCodecActualFamily.components.flatMap Air.Table.exprs:=
    List.mem_flatMap.mpr ⟨T,hT,he⟩
  rw [exprs_eq] at hm
  obtain ⟨U,hU,heU⟩:=List.mem_flatMap.mp hm
  exact ⟨ProcPriorVertical4DataEval.component_columns U hU e heU,
    ProcPriorOverlayDataTransport.component_pub U hU e heU⟩

theorem padding (T : Air.Table) (hT:T∈ProcPriorCodecActualFamily.components)
    (next : Nat→Fp) (first last trans : Fp)
    (a : Interaction) (ha:a∈T.interactions) (e : Expr) (he:e∈a.mult) :
    e.evalWith (env (fun _=>0) next first last trans)=0 := by
  have hm:e∈ProcPriorCodecActualFamily.components.flatMap
      (fun T=>T.interactions.flatMap Interaction.mult):=
    List.mem_flatMap.mpr ⟨T,hT,List.mem_flatMap.mpr ⟨a,ha,he⟩⟩
  rw [mults_eq] at hm
  obtain ⟨U,hU,hmU⟩:=List.mem_flatMap.mp hm
  obtain ⟨b,hb,heU⟩:=List.mem_flatMap.mp hmU
  exact ProcPriorOverlayPadding.multiplicity U hU next first last trans b hb e heU
end ZkFormal.NearV3.Candidates.ProcPriorOverlayActualExprs
