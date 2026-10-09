import ZkFormal.NearV3.Candidates.ProcIdTaggedPublic
import ZkFormal.NearV3.Candidates.ProcCodecPublicIdPacked
import ZkFormal.NearV3.Candidates.ProcCodecConcatTraffic
namespace ZkFormal.NearV3.Candidates.ProcNativePublicIdBalance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest

theorem block (b : NativeBlock) (hb:b.Valid) (hd:b.run.n=b.pub.ids.length)
    (hn:0<b.run.n) (h64:b.run.n≤64) (hi:∀id∈b.pub.ids,id<2^64) :
    b.output.rows.toList.flatMap (fun row=>ProcCodecConcatTraffic.natMessages row 70 true)=
    ProcIdTaggedPublic.packets b.run.tau b.pub.ids := by
  have hs:=native_block_length b hb h64
  rw [←ProcCodecConcatTraffic.physical b.output.rows (by omega) 0 70 [] true,
    ProcCodecPublicIdInventory.physical _ _ _ _ _ _ _ hb.2.2.2.2 hn h64,hd]
  unfold ProcIdTaggedPublic.packets
  apply List.map_congr_left
  intro s hmem
  apply ProcCodecPublicIdPacked.message
  apply hi
  change b.pub.ids.getD s 0∈b.pub.ids
  have h:=List.mem_range.mp hmem
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
  exact List.getElem_mem h

theorem prepared_blocks {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (bs : List NativeBlock) (hlen:bs.length≤32)
    (hb:∀b∈bs,b.Valid ∧ b.pub∈p.sched ∧
      ∃tauV,ActualRun.run (ProcPreparedSequence.input b.pub b.old) tauV=.ok b.run)
    (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) t r pub 70 true)=
    bs.flatMap (fun b=>ProcIdTaggedPublic.packets b.run.tau b.pub.ids) := by
  have hh:∀b∈bs,b.Valid ∧ b.run.n=b.pub.ids.length ∧ 0<b.run.n ∧ b.run.n≤64 := by
    intro b hm
    obtain ⟨hv,hsp,tauV,hr⟩:=hb b hm
    have hf:=ProcActualRunProjection.run_fields _ _ _ hr
    have hn:b.run.n=b.pub.ids.length:=hf.2.1
    have hs:=prepD0_sched hp b.pub hsp
    exact ⟨hv,hn,by have :=hs.n1;omega,by have :=hs.n64;omega⟩
  have hs:=native_block_rows_bound bs (fun b hm=>⟨(hh b hm).1,(hh b hm).2.2.2⟩)
  rw [ProcCodecConcatTraffic.blocks bs (by omega)]
  apply ProcCodecPublicIdEnumeration.flat_congr
  intro b hm
  obtain ⟨hv,hd,hn,h64⟩:=hh b hm
  exact block b hv hd hn h64 (prepD0_ids64 hp b.pub (hb b hm).2.1)

/-- Same actual prepared layouts, without an external input equality or ID uniqueness premise. -/
theorem balance {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (bs : List NativeBlock) (hlen:bs.length≤32)
    (hb:∀b∈bs,b.Valid ∧ b.pub∈p.sched ∧
      ∃tauV,ActualRun.run (ProcPreparedSequence.input b.pub b.old) tauV=.ok b.run)
    (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184)
    (tc ti : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub 70 true msg=
    tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs)) ti pub 70 false msg := by
  have hi:∀b∈bs,b.pub.ids.length≤64:=by
    intro b hm
    exact (prepD0_sched hp b.pub (hb b hm).2.1).n64
  have hc:=ProcNativeIdBalance.native_capacity (fun b=>b.pub.ids) bs hi hlen hraw
  rw [ProcIdTaggedPublic.count _ bs (by omega),tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=_
  rw [prepared_blocks hp bs hlen hb]
end ZkFormal.NearV3.Candidates.ProcNativePublicIdBalance
