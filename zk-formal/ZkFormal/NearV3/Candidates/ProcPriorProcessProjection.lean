import ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedSound
import ZkFormal.NearV3.Candidates.ProcPriorProcessTransport
import ZkFormal.NearV3.Candidates.HorizontalProjection
namespace ZkFormal.NearV3.Candidates.ProcPriorProcessProjection
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorProcessRepairedFamily
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def offset (i : Nat) : Nat:=((ProcPriorComparatorRoutedFamily.selected.take i).map (·.width)).sum

theorem layout_member (ts : List Air.Table) (off i : Nat) (hi:i<ts.length) :
    HorizontalTables.shifted (off+((ts.take i).map (·.width)).sum) ts[i]!∈HorizontalTables.layout off ts := by
  induction ts generalizing off i with
  | nil=>simp at hi
  | cons T ts ih=>
    cases i with
    | zero=>simp [HorizontalTables.layout]
    | succ i=>
      have hm:=ih (off+T.width) i (by simpa using hi)
      apply List.mem_cons_of_mem
      simpa [List.take_succ_cons,Nat.add_assoc] using hm

theorem location (i : Nat) (hi:i<selected.length) :
    HorizontalTables.shifted (offset i) (selected[i]!)∈HorizontalTables.layout 0 selected := by
  have he:((selected.take i).map (·.width)).sum=offset i := by
    unfold offset
    rw [ List.map_take, List.map_take,widths]
  have hm:=layout_member selected 0 i hi
  simpa only [Nat.zero_add,he] using hm

theorem cap (i : Nat) (hi:i<selected.length) : (selected[i]!).maxLog=22 := by
  have hall:(List.range 20).all (fun i=>decide ((selected[i]!).maxLog=22))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hall i (List.mem_range.mpr hi))

theorem raw_local (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal fused tr t pub) : TableLocal raw tr t pub := by
  have hp:= (InteractionTriples.local_iff paired tr t pub).mp h
  exact (InteractionPairing.local_iff raw tr t pub).mp hp

/-- Existing non-process extractors consume their unchanged table on the exact
old column projection. No old-family Holds premise is manufactured. -/
theorem nonprocess_local (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal fused tr t pub) (i : Nat) (hi:i<selected.length) (hne:i≠10) :
    TableLocal (ProcPriorComparatorRoutedFamily.selected[i]!)
      (HorizontalTrace.project (offset i) tr) t pub := by
  have hh:=HorizontalTrace.project_local (location i hi) (cap i hi) (raw_local tr t pub h)
  rwa [other_slot i hne] at hh

theorem process_local (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal fused tr t pub) :
    TableLocal ProcBoundaryRepair.table (HorizontalTrace.project (offset 10) tr) t pub := by
  have hh:=HorizontalTrace.project_local (location 10 (by decide +kernel))
    (cap 10 (by decide +kernel)) (raw_local tr t pub h)
  rwa [process_slot] at hh
end ZkFormal.NearV3.Candidates.ProcPriorProcessProjection
