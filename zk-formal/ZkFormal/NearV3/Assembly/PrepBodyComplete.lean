import ZkFormal.NearV3.Assembly.PrepContext
import ZkFormal.NearV3.Assembly.HeaderCompose
import ZkFormal.NearV3.Assembly.ReceiptWellformed
import ZkFormal.NearV3.Assembly.ForwardDemand

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def nativeHint (k : WalkD0) (w : StateWitness) (m : MainExecutionV3) : Hint :=
  ⟨(appliedReceipts k w).length,u32 0 ++ encodeReceipts m.result.outgoing⟩

theorem prepBody_native_success {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {pc : PrepC} {last : Bytes} {raw : Bytes}
    (hc : NativePrepContext k m pc) (hm : m.NativeValid k w)
    (hh : NativeHeaderV3 k m last) (hd : decodeStateWitness raw = .ok w)
    (hg : k.slotB2.gasLimit ≤ maxGasLimitD0) :
    ∃ p, prepBody pc (nativeHint k w m) = .ok p ∧ p.body = (nativeHint k w m).body := by
  have hbody := hm.body_decodes hd hg
  have hstatus := applyNewChunk_status_guard hm.run
  have hgas := applyNewChunk_fwdGasOk hm.run
  have hdemand := applyNewChunk_fwdDemand_guard hm.run
  have hcompute := applyNewChunk_compute_guard hm.run
  have hused := applyNewChunk_gas hm.run
  have hused' : k.H.prevGasUsed = (appliedReceipts k w).length * NearSpec.Params.G :=
    hh.gasUsed.trans hused
  refine ⟨{
    hdr := {pc.hdr with n := (appliedReceipts k w).length}, lists := pc.lists,
    bnds := pc.bnds,sched := pc.sched,body := (nativeHint k w m).body,
    fwd := fwdLinks pc.ctxB2 m.result.outgoing},?_,rfl⟩
  simp only [prepBody,nativeHint,hbody,hc.ctx,hstatus,hgas,hdemand,hcompute,
    hc.header,hc.layout,hc.gasLimit,hc.congestion,hc.allowed,hc.rsData,hc.rsTotal,
    hh.proposals,hh.gasLimit,hused',hh.outgoingRoot,hh.congestion,hh.bandwidthRequests,
    hh.split,hh.txRoot,hh.encoded,check,beq_self_eq_true,↓reduceIte,
    pure,Except.pure,bind,Except.bind]

theorem prepD0_native_success {cb : Bytes} {pc : PrepC} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {last : Bytes} {raw : Bytes}
    (hp : prepClaim cb = .ok pc) (hk : walkD0 cb = .ok k) (hm : m.NativeValid k w)
    (hh : NativeHeaderV3 k m last) (hd : decodeStateWitness raw = .ok w)
    (hg : k.slotB2.gasLimit ≤ maxGasLimitD0) :
    ∃ p, prepD0 cb (nativeHint k w m) = .ok p ∧
      HeaderSemanticsV3 k (nativeHint k w m) p m last := by
  obtain ⟨p,hbody,hpb⟩ := prepBody_native_success (prepClaim_native_context hp hk hm) hm hh hd hg
  refine ⟨p,?_,hh.prepared _ _ rfl hpb⟩
  simpa only [prepD0,hp,bind,Except.bind] using hbody

end ZkFormal.NearV3.Assembly
