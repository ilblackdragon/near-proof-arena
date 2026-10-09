import ZkFormal.NearV3.Assembly.SchedulerPriorOverlayExternal
import ZkFormal.NearV3.Assembly.SchedulerPriorUniformTraffic
import ZkFormal.NearV3.Candidates.ProcCodecParameterTraffic
import ZkFormal.NearV3.Candidates.ProcRecordParameterTraffic
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem PriorCore.parameter_balance {B : Nat} {p : Prep} {bs : List NativeBlock}
    (hc:PriorCore p B bs) (hB:B≤2000000) (tc tr : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub 76 true msg=
    tableBusCount (ProcPriorRecordLinear.interactions 75 71 72 67 76)
      (ProcRecordConcatTraffic.trace (fun b=>b.pub.ids) bs) tr pub 76 false msg := by
  have hrows:=native_block_rows_bound bs hc.valid
  have hlen:=hc.length
  have hraw:=hc.raw_bound
  have hcap:=ProcRecordConcatTraffic.capacity (fun b=>b.pub.ids) bs
  have hn:∀b∈bs,b.run.n=b.pub.ids.length := by
    intro b hb
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    exact (ProcActualRunProjection.run_fields _ _ _ (hc.indexed i b hi).1.2).2.1
  rw [tableBusCount_eq,tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=((List.range (2^22)).flatMap _).count msg
  rw [ProcCodecConcatTraffic.blocks bs (by omega),ProcRecordParameterTraffic.physical _ bs (by omega)]
  apply congrArg (fun (xs : List (List Fp))=>xs.count msg)
  rw [List.map_eq_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro b hb
  have hv:=(hc.valid b hb).1
  have hs:=native_block_length b hv (hc.valid b hb).2
  rw [←ProcCodecConcatTraffic.physical b.output.rows (by omega) tc 76 pub true,
    ProcCodecParameterTraffic.physical _ _ _ _ _ _ _ hv.2.2.2.2,hn b hb]

theorem routed_parameter_balance {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (tc to : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub 76 true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) to pub 76 false msg := by
  have ho:=overlay_unique_count hp bs hc hB to pub 76 (by decide) (by decide) false msg 3 (by decide) (by
    intro j hj hn
    have hh:j=0∨j=1∨j=2:=by omega
    rcases hh with rfl|rfl|rfl <;> decide +kernel)
  have hc0:tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub 76 true msg=
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 76 true msg :=
    (ProcPriorComparatorRouting.other_count ProcPriorCodecActual.table.interactions _ tc pub 76
      (by decide) (by decide) true msg).trans (codec_count_stable bs tc pub 76 true msg)
  have hb:tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 76 true msg=
    componentCount bs 3 76 false msg := hc.parameter_balance hB 0 0 [] msg
  exact hc0.trans (hb.trans ho.symm)
end ZkFormal.NearV3.Assembly.CodecDigest
