import ZkFormal.NearV3.Candidates.ProcPriorCodecActualFamily
import ZkFormal.NearV3.Candidates.HorizontalProjection
import ZkFormal.NearV3.Candidates.ProcPriorVerticalReadSound
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyProjection
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768

/-- Triple packing and pairing preserve the actual family's constraint list. -/
theorem constraints_same :
    (ProcPriorCodecActualFamily.tables[0]!).constraints=ProcPriorCodecActualFamily.raw.constraints := rfl

theorem overlay_constraints :ProcPriorCodecActualFamily.overlay.constraints=
    ProcPriorVertical4Linear.table.constraints := rfl

theorem overlay_member :ProcPriorCodecActualFamily.overlay∈ProcPriorCodecActualFamily.selected := by
  have he:ProcPriorCodecActualFamily.selected[19]?=some ProcPriorCodecActualFamily.overlay := rfl
  exact List.mem_iff_getElem?.mpr ⟨19,he⟩

/-- Locate and extract an actual component's constraints from arbitrary fused
local validity. Projection retains the physical row clock and adjacency. -/
theorem component_local {ts : List Air.Table} {T : Air.Table} {tr : Trace Fp}
    {t : Nat} {pub : List Fp} (hm:T∈ts)
    (hL:Local (HorizontalTables.fuse ts).constraints tr t pub) :
    ∃off,HorizontalTables.shifted off T∈HorizontalTables.layout 0 ts ∧
      Local T.constraints (HorizontalTrace.project off tr) t pub := by
  have hx:T∈(HorizontalProjection.split tr 0 ts).map Prod.fst := by
    rw [HorizontalProjection.split_tables];exact hm
  obtain ⟨x,hx,he⟩:=List.mem_map.mp hx
  obtain ⟨off,hloc,_⟩:=HorizontalProjection.split_location ts tr 0 hx
  rw [he] at hloc
  refine ⟨off,hloc,?_⟩
  intro r hr e hem
  rw [←HorizontalTrace.expression_eval]
  exact hL r hr _ (List.mem_flatMap.mpr ⟨HorizontalTables.shifted off T,hloc,List.mem_map.mpr ⟨e,hem,rfl⟩⟩)

/-- The actual paired/triple-packed family yields arbitrary vertical Local,
without a caller-supplied layout, offset, generated trace or window. -/
theorem overlay_local {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:Local (ProcPriorCodecActualFamily.tables[0]!).constraints tr t pub) :
    ∃off,HorizontalTables.shifted off ProcPriorCodecActualFamily.overlay∈
      HorizontalTables.layout 0 ProcPriorCodecActualFamily.selected ∧
      ProcPriorVerticalMemorySound.LocalV (HorizontalTrace.project off tr) t pub := by
  rw [constraints_same] at hL
  obtain ⟨off,hloc,hL⟩:=component_local overlay_member hL
  rw [overlay_constraints] at hL
  exact ⟨off,hloc,hL⟩

/-- Actual full-family validity discharges the outer horizontal local premise;
public/global traffic is deliberately not reconstructed by this lemma. -/
theorem holds_overlay {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (ht:0<AP.tables.length)
    (htab:AP.tables[0]! =ProcPriorCodecActualFamily.tables[0]!) :
    ∃off,HorizontalTables.shifted off ProcPriorCodecActualFamily.overlay∈
      HorizontalTables.layout 0 ProcPriorCodecActualFamily.selected ∧
      ProcPriorVerticalMemorySound.LocalV (HorizontalTrace.project off tr) 0 pub := by
  have hL:=local_of_holdsP hH ht
  rw [htab] at hL
  exact overlay_local hL
end ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyProjection
