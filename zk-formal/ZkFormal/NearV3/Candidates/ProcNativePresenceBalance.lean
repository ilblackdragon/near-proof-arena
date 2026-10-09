import ZkFormal.NearV3.Candidates.ProcRawPresenceList
import ZkFormal.NearV3.Candidates.ProcCodecConcatTraffic
namespace ZkFormal.NearV3.Candidates.ProcNativePresenceBalance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest

theorem block_messages (b : NativeBlock) (hb:b.Valid) (hn:b.run.n≤64) :
    b.output.rows.toList.flatMap (fun row=>ProcCodecConcatTraffic.natMessages row B_SPOST true)=
      [ProcRawPresenceList.packet b] := by
  have hc:b.output.rows.size≤2^22 := by have:=native_block_length b hb hn; omega
  rw [←ProcCodecConcatTraffic.physical _ hc 0 B_SPOST [] true,
    ProcCodecPresencePhysical.physical _ _ _ _ _ _ _ hb.2.2.2.2]
  unfold ProcRawPresenceList.packet
  cases b.prior <;> rfl

theorem codec_physical (bs : List NativeBlock) (hb:∀b∈bs,b.Valid ∧ b.run.n≤64)
    (hlen:bs.length≤32) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) t r pub B_SPOST true)=
      bs.map ProcRawPresenceList.packet := by
  have hc:(nativeBlockRows bs).size≤2^22 := by have:=native_block_rows_bound bs hb; omega
  rw [ProcCodecConcatTraffic.blocks bs hc]
  have hm:bs.flatMap (fun b=>b.output.rows.toList.flatMap (fun row=>ProcCodecConcatTraffic.natMessages row B_SPOST true))=
      bs.flatMap (fun b=>[ProcRawPresenceList.packet b]) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro b hmem
    exact block_messages b (hb b hmem).1 (hb b hmem).2
  rw [hm,←List.map_eq_flatMap]

/-- Whole physical corrected Codec/RawFrame presence conservation on SAME
ordered native blocks; both streams retain every absent-state packet. -/
theorem balance (bs : List NativeBlock) (hb:∀b∈bs,b.Valid ∧ b.run.n≤64)
    (hlen:bs.length≤32) (hcap:(ProcRawConcatGeometry.rows bs).length≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) t pub B_SPOST true msg=
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (ProcRawConcatGeometry.trace bs) t pub B_SPOST false msg := by
  rw [ProcRawPresenceList.count bs hcap,tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (codec_physical bs hb hlen t pub)
end ZkFormal.NearV3.Candidates.ProcNativePresenceBalance
