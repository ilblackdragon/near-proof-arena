import ZkFormal.NearV3.Assembly.SchedulerPriorInstalled
import ZkFormal.NearV3.Candidates.ProcCodecConcatTraffic
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem codec_count_stable (bs : List NativeBlock) (t : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool) (msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) t pub bus sd msg=
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] bus sd msg := by
  simp only [tableBusCount_eq,ProcCodecConcatTraffic.row_messages]
  rfl

theorem routed_codec_count_stable (bs : List NativeBlock) (t : Nat) (pub : List Fp)
    (bus : Nat) (h69:bus≠69) (h40:bus≠40) (sd : Bool) (msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) t pub bus sd msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] bus sd msg := by
  apply Eq.trans (ProcPriorComparatorRouting.other_count ProcPriorCodecActual.table.interactions _ t pub bus h69 h40 sd msg)
  apply Eq.trans (codec_count_stable bs t pub bus sd msg)
  exact (ProcPriorComparatorRouting.other_count ProcPriorCodecActual.table.interactions _ 0 [] bus h69 h40 sd msg).symm

/-- External joins survive arbitrary horizontal installation time and public
vector, rather than relying on the component's canonical time0/empty vector. -/
theorem PriorInstalled.outgoing_uniform {bs : List NativeBlock} (hi:PriorInstalled bs)
    (bus : Nat) (hb:bus∈[60,70]) (tc to : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub bus true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) to pub bus false msg := by
  have hb':bus=60∨bus=70:=by simpa using hb
  exact (routed_codec_count_stable bs tc pub bus (by omega) (by omega) true msg).trans
    (hi.outgoing bus hb to pub msg)

theorem PriorInstalled.read_uniform {bs : List NativeBlock} (hi:PriorInstalled bs)
    (tc to : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) to pub 68 true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub 68 false msg := by
  exact (hi.read to pub msg).trans
    (routed_codec_count_stable bs tc pub 68 (by decide) (by decide) false msg).symm
end ZkFormal.NearV3.Assembly.CodecDigest
