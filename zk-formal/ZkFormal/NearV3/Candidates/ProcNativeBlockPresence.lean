import ZkFormal.NearV3.Candidates.ProcRawInstancePresence
import ZkFormal.NearV3.Assembly.SchedulerCodecMissingBlock
namespace ZkFormal.NearV3.Candidates.ProcNativeBlockPresence
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly.CodecDigest

theorem presence (b : NativeBlock) (hb : b.Valid) (time : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions (SchedHeight.trace b.output.rows codecPad)
      time pub B_SPOST true msg =
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (ProcRawInstancePresence.traceAt b.run.tau b.old b.vid b.prior.isSome)
      time pub B_SPOST false msg := by
  rw [ProcCodecPresencePhysical.count _ _ _ _ _ _ _ hb.2.2.2.2,
    ProcRawInstancePresence.count]
  cases b.prior <;> rfl

/-- A valid native block's present read is exactly the bytes rendered by its
raw parser. Record order, duplicate keys and arbitrary count are preserved. -/
theorem original_bytes (b : NativeBlock) (hb : b.Valid) (bs : Bytes)
    (h : b.prior=some bs) : bs=b.old.encode := by
  have hd:=hb.2.2.2.1
  rw [h] at hd
  exact (ProcPriorDecode.decode_exact bs b.old hd).2.2.2

theorem present_bytes (b : NativeBlock) (hb : b.Valid) (bs : Bytes)
    (h : b.prior=some bs) (hfit : bs.length≤2^22)
    (time : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (ProcRawInstancePresence.traceAt b.run.tau b.old b.vid b.prior.isSome)
      time pub B_VBYTES true msg = cnt (emitAt b.vid 0 (bs.map UInt8.toNat)) msg := by
  rw [ProcRawInstancePresence.bytes_count,h]
  change tableBusCount (ProcPriorRawFrame.interactions ZkFormal.NearV3.Sched.B_SPOST 73 B_VBYTES 74 75)
    (ProcPriorRawGen.trace b.old b.vid true) time pub B_VBYTES true msg=_
  have hd:=hb.2.2.2.1
  rw [h] at hd
  exact ProcPriorRawByteTraffic.decoded_count bs b.old b.vid time pub msg hd hfit

/-- Missing state supplies no invented authenticated bytes. -/
theorem absent_bytes (b : NativeBlock) (hb : b.Valid) (h : b.prior=none)
    (time : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (ProcRawInstancePresence.traceAt b.run.tau b.old b.vid b.prior.isSome)
      time pub B_VBYTES true msg =0 := by
  rw [ProcRawInstancePresence.bytes_count,h,tableBusCount_eq]
  have hd:=hb.2.2.2.1
  rw [h] at hd
  have he:b.old=Bandwidth.State.initial := (Option.some.inj hd).symm
  rw [he]
  change ((List.range (2^22)).flatMap (fun r=>rowTraffic
    (ProcPriorRawFrame.interactions ZkFormal.NearV3.Sched.B_SPOST 73 B_VBYTES 74 75)
    (ProcPriorRawGen.trace Bandwidth.State.initial b.vid false) time r pub B_VBYTES true)).count msg=0
  rw [ProcPriorRawByteTraffic.physical _ _ _ _ _ (by decide +kernel)]
  rfl
end ZkFormal.NearV3.Candidates.ProcNativeBlockPresence
