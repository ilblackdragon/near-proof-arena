import ZkFormal.NearV3.Assembly.SchedulerPriorInstalled
import ZkFormal.NearV3.Candidates.HorizontalTraffic
import ZkFormal.NearV3.Candidates.InteractionTriplesTransport
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def priorSelectedTrace (bs : List NativeBlock) (other : Nat→Trace Fp) (i : Nat) : Trace Fp :=
  if i=8 then SchedHeight.trace (nativeBlockRows bs) codecPad
  else if i=19 then priorOverlay bs else other i

def priorSelectedParts (bs : List NativeBlock) (other : Nat→Trace Fp) : List (Air.Table×Trace Fp) :=
  ProcPriorComparatorRoutedFamily.selected.zipIdx.map
    (fun (T,i)=>(T,priorSelectedTrace bs other i))

def priorFusedTrace (bs : List NativeBlock) (other : Nat→Trace Fp) : Trace Fp :=
  HorizontalAssembly.trace (fun _=>22) (priorSelectedParts bs other)

theorem selected_caps :ProcPriorComparatorRoutedFamily.selected.all (fun T=>T.maxLog≤22)=true := by
  decide +kernel

theorem selected_columns :ProcPriorComparatorRoutedFamily.selected.all
    (fun T=>T.exprs.all (fun e=>e.colBound≤T.width))=true := by
  decide +kernel

theorem selected_parts_tables (bs : List NativeBlock) (other : Nat→Trace Fp) :
    (priorSelectedParts bs other).map Prod.fst=ProcPriorComparatorRoutedFamily.selected := by
  simp only [priorSelectedParts,List.map_map]
  exact List.zipIdx_map_fst 0 _

theorem selected_trace_log (bs : List NativeBlock) (other : Nat→Trace Fp) (i t : Nat)
    (ho:∀j,j≠8→j≠19→(other j).log t=22) : (priorSelectedTrace bs other i).log t=22 := by
  by_cases h8:i=8
  · simp only [priorSelectedTrace,h8,ite_true];rfl
  · by_cases h19:i=19
    · simp only [priorSelectedTrace,h19,ite_true];rfl
    · simp only [priorSelectedTrace,h8,h19,ite_false]
      exact ho i h8 h19

/-- Actual selected Codec and prior overlay are inserted in the full column
layout. Remaining selected witnesses must supply their own local proofs. -/
theorem prior_fused_local (bs : List NativeBlock) (hi:PriorInstalled bs)
    (other : Nat→Trace Fp) (t : Nat) (pub : List Fp)
    (ho:∀j,j≠8→j≠19→(other j).log t=22)
    (hl:∀T j,(T,j)∈ProcPriorComparatorRoutedFamily.selected.zipIdx→j≠8→j≠19→
      TableLocal T (other j) t pub) :
    TableLocal ProcPriorComparatorRoutedFamily.fused (priorFusedTrace bs other) t pub := by
  apply (InteractionTriples.local_iff _ _ _ _).mpr
  apply (InteractionPairing.local_iff _ _ _ _).mpr
  change TableLocal (HorizontalTables.fuse ProcPriorComparatorRoutedFamily.selected) _ _ _
  rw [←selected_parts_tables bs other]
  apply HorizontalAssembly.trace_local _ _ t pub (by decide)
  · intro x hx
    obtain ⟨⟨T,j⟩,hj,rfl⟩:=List.mem_map.mp hx
    exact selected_trace_log bs other j t ho
  · intro x hx
    have hm:x.1∈ProcPriorComparatorRoutedFamily.selected:=by
      rw [←selected_parts_tables bs other]
      exact List.mem_map.mpr ⟨x,hx,rfl⟩
    exact of_decide_eq_true (List.all_eq_true.mp selected_caps x.1 hm)
  · intro x hx
    obtain ⟨⟨T,j⟩,hj,rfl⟩:=List.mem_map.mp hx
    have he:=List.mk_mem_zipIdx_iff_getElem?.mp hj
    by_cases h8:j=8
    · subst j
      have ht:T=ProcPriorComparatorRoutedFamily.selected[8]!:=by
        exact (List.getElem!_of_getElem? he).symm
      subst T
      exact hi.codec_local t pub
    · by_cases h19:j=19
      · subst j
        have ht:T=ProcPriorComparatorRoutedFamily.selected[19]!:=by
          exact (List.getElem!_of_getElem? he).symm
        subst T
        exact hi.overlay_local t pub
      · simpa only [priorSelectedTrace,h8,h19,ite_false] using hl T j hj h8 h19
  · intro x hx e he
    have hm:x.1∈ProcPriorComparatorRoutedFamily.selected:=by
      rw [←selected_parts_tables bs other]
      exact List.mem_map.mpr ⟨x,hx,rfl⟩
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp selected_columns x.1 hm) e he)

/-- Column installation, pair reordering and triple padding preserve exact
natural traffic counts on every bus, including repeated messages. -/
theorem prior_fused_count (bs : List NativeBlock) (other : Nat→Trace Fp)
    (t : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) (msg : List Fp)
    (ho:∀j,j≠8→j≠19→(other j).log t=22) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions
      (priorFusedTrace bs other) t pub bus sd msg=
    ((priorSelectedParts bs other).map (fun x=>tableBusCount x.1.interactions x.2 t pub bus sd msg)).sum := by
  apply Eq.trans (InteractionTriples.table_traffic ProcPriorComparatorRoutedFamily.paired _ t pub bus sd msg)
  apply Eq.trans (InteractionPairing.count ProcPriorComparatorRoutedFamily.raw.interactions _ t pub bus sd msg)
  have hclock:∀x∈priorSelectedParts bs other,x.2.log t=(fun _=>22) t := by
    intro x hx
    obtain ⟨⟨T,j⟩,hj,rfl⟩:=List.mem_map.mp hx
    exact selected_trace_log bs other j t ho
  have hcap:∀x∈priorSelectedParts bs other,x.1.maxLog≤22 := by
    intro x hx
    have hm:x.1∈ProcPriorComparatorRoutedFamily.selected:=by
      rw [←selected_parts_tables bs other]
      exact List.mem_map.mpr ⟨x,hx,rfl⟩
    exact of_decide_eq_true (List.all_eq_true.mp selected_caps x.1 hm)
  have hcols:∀x∈priorSelectedParts bs other,∀e∈x.1.exprs,e.colBound≤x.1.width := by
    intro x hx e he
    have hm:x.1∈ProcPriorComparatorRoutedFamily.selected:=by
      rw [←selected_parts_tables bs other]
      exact List.mem_map.mpr ⟨x,hx,rfl⟩
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp selected_columns x.1 hm) e he)
  have hh:=HorizontalTraffic.trace_count (fun _=>22) (priorSelectedParts bs other)
    t pub bus sd msg hclock hcap hcols
  simpa only [selected_parts_tables,ProcPriorComparatorRoutedFamily.raw,priorFusedTrace] using hh
end ZkFormal.NearV3.Assembly.CodecDigest
