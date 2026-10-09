import ZkFormal.NearV3.Assembly.SchedulerPriorUniformTraffic
import ZkFormal.NearV3.Candidates.ProcRawSanityTraffic
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem native_sanity_byte (b : NativeBlock) (hb:b.Valid) (g : Nat) :
    (b.old.sanityHash.getD g 0).toNat=
    ProcCodecSanityTraffic.priorByte (ProcPreparedSequence.input b.pub b.old) b.prior.isSome g := by
  cases hp:b.prior with
  | none=>
    have hd:=hb.2.2.2.1
    rw [hp] at hd
    have he:b.old=Bandwidth.State.initial:=(Option.some.inj hd).symm
    rw [he]
    have hz:Bandwidth.State.initial.sanityHash=List.replicate 32 (0:UInt8):=rfl
    rw [hz]
    have hzget (n j : Nat) : (List.replicate n (0:UInt8)).getD j 0=0 := by
      induction n generalizing j with
      | zero => rfl
      | succ n ih =>
        cases j with
        | zero => rfl
        | succ j => exact ih j
    rw [hzget]
    simp only [ProcCodecSanityTraffic.priorByte,Option.isSome_none]
    rfl
  | some raw=>
    simp only [ProcCodecSanityTraffic.priorByte,ProcPreparedSequence.input,Option.isSome_some,ite_true]
    rw [List.getElem!_eq_getElem?_getD,List.getElem?_map,List.getD_eq_getElem?_getD]
    cases b.old.sanityHash[g]? <;> rfl

theorem PriorCore.sanity_balance {B : Nat} {p : Prep} {bs : List NativeBlock}
    (hc:PriorCore p B bs) (hB:B≤2000000) (tc tr : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (ProcRawConcatGeometry.trace bs) tr pub 74 true msg=
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub 74 false msg := by
  have hrows:=native_block_rows_bound bs hc.valid
  have hlen:=hc.length
  have hraw:=hc.raw_bound
  rw [tableBusCount_eq,tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=((List.range (2^22)).flatMap _).count msg
  rw [ProcRawSanityTraffic.physical bs (by omega),ProcCodecConcatTraffic.blocks bs (by omega)]
  apply congrArg (fun (xs:List (List Fp))=>xs.count msg)
  apply congrArg List.flatten
  apply List.map_congr_left
  intro b hb
  have hv:=(hc.valid b hb).1
  have hn:=(hc.valid b hb).2
  have hs:=native_block_length b hv hn
  rw [←ProcCodecConcatTraffic.physical b.output.rows (by omega) tc 74 pub false,
    ProcCodecSanityTraffic.physical _ _ _ _ _ _ _ hv.2.2.2.2 hn]
  apply List.map_congr_left
  intro g hg
  rw [native_sanity_byte b hv g]

theorem routed_sanity_balance {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (tc to : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
      (priorOverlay bs) to pub 74 true msg=
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub 74 false msg := by
  have ho:=overlay_unique_count hp bs hc hB to pub 74 (by decide) (by decide) true msg 2 (by decide) (by
    intro j hj hn
    have hh:j=0∨j=1∨j=3:=by omega
    rcases hh with rfl|rfl|rfl <;> decide +kernel)
  have hb:componentCount bs 2 74 true msg=
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) 0 [] 74 false msg:=hc.sanity_balance hB 0 0 [] msg
  have hco:=codec_count_stable bs tc pub 74 false msg
  have hr:=ProcPriorComparatorRouting.other_count ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub 74 (by decide) (by decide) false msg
  exact ho.trans (hb.trans (hco.symm.trans hr.symm))
end ZkFormal.NearV3.Assembly.CodecDigest
