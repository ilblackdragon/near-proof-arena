import ZkFormal.NearV3.Assembly.SchedulerCodecRawAccepted
import ZkFormal.NearV3.Candidates.ProcNativePresenceBalance
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Same accepted execution, same blocks, both physical local tables and
exact physical presence conservation. Other buses remain separate. -/
theorem accepted {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (h : checkD0a B cb wb=.ok ()) (hB:B≤2000000) (vids : Nat→Nat) :
    ∃bs : List NativeBlock,bs.length≤32 ∧
      (∀b∈bs,b.Valid ∧ b.run.n≤64) ∧
      (∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i) ∧
      (ProcRawConcatGeometry.rows bs).length≤B+1184 ∧
      (∀time pub,TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace (nativeBlockRows bs) codecPad) time pub ∧
        TableLocal (ProcPriorRawFrame.table B_SPOST 73 B_VBYTES 74 75)
          (ProcRawConcatGeometry.trace bs) time pub) ∧
      ∀time pub msg,tableBusCount ProcPriorCodecActual.table.interactions
        (SchedHeight.trace (nativeBlockRows bs) codecPad) time pub B_SPOST true msg=
        tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
          (ProcRawConcatGeometry.trace bs) time pub B_SPOST false msg := by
  obtain ⟨bs,hlen,hvalid,horder,hraw,hcodec,hparser⟩:=accepted_tables hp hk hw h hB vids
  refine ⟨bs,hlen,hvalid,horder,hraw,?_,?_⟩
  · intro time pub
    exact ⟨hcodec time pub,hparser time B_SPOST 73 B_VBYTES 74 75 pub⟩
  · exact ProcNativePresenceBalance.balance bs hvalid hlen (by omega)
end ZkFormal.NearV3.Assembly.CodecDigest
