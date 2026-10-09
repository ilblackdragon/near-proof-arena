import ZkFormal.NearV3.Candidates.ProcNativeForwardRuntime
import ZkFormal.NearV3.Candidates.ProcNativeForwardInitial
namespace ZkFormal.NearV3.Candidates.ProcNativeForwardCodec
open NearSpec NearSpecV3 NearSpec.TransferV1
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- Concrete receipt execution supplies every forwarding guard once scheduler
ID lookup agrees with the process-memory and distribution grant columns. -/
theorem runtime_demands (prims : Prims) (ctx : ApplyCtx) (so : SchedOut)
    (rs : List Receipt) (i : Nat) (acc : Acc) (out : Acc×List Limit)
    (h : applyReceipts ctx i (acc,ProcNativeForwardInitial.limits prims ctx so) rs=.ok out)
    (R : Run) (gb : Array Nat)
    (hg : ∀o,Scheduler.indexOf ctx.layout.shardIds ctx.own=some o →
      ∀s r,Scheduler.indexOf ctx.layout.shardIds s=some r →
        so.grant ctx.own s≤(R.segs.getD (o*ctx.layout.shardIds.length+r) default).wfin+
          gb[o*ctx.layout.shardIds.length+r]!) :
    ProcPriorCodecForwardBound.Demands R gb
      (fwdLinks ctx (out.1.refunds.drop acc.refunds.length)) := by
  have hf := ProcNativeForwardRuntime.appended_refunds ctx rs i
    (acc,ProcNativeForwardInitial.limits prims ctx so) out h
  apply ProcPriorCodecForwardBound.native_links
  intro o ho d hd r hr
  exact Nat.le_trans (ProcNativeForwardInitial.demand_grant prims ctx so _ out.2 hf d hd)
    (hg o ho d.1 r hr)
open Scheduler in
theorem codec_success (sp : SchedPub) (hs : SchedPubOk sp)
    (old : Option Bytes) (prev : Bandwidth.State)
    (hd : ProcActualCore.decodePrevious old=some prev) (tau : Nat) (R : Run)
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R)
    (prims : Prims) (ctx : ApplyCtx) (so : SchedOut)
    (rs : List Receipt) (i : Nat) (acc : Acc) (out : Acc×List Limit)
    (h : applyReceipts ctx i (acc,ProcNativeForwardInitial.limits prims ctx so) rs=.ok out)
    (vid : Nat) (gb : Array Nat)
    (hg : ∀o,Scheduler.indexOf ctx.layout.shardIds ctx.own=some o →
      ∀s r,Scheduler.indexOf ctx.layout.shardIds s=some r →
        so.grant ctx.own s≤(R.segs.getD (o*ctx.layout.shardIds.length+r) default).wfin+
          gb[o*ctx.layout.shardIds.length+r]!) :
    ∃result,ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R old.isSome vid gb
      (fwdLinks ctx (out.1.refunds.drop acc.refunds.length))=.ok result :=
  ProcPriorCodecForwardBound.decoded_codec sp hs old prev hd tau R hr vid gb _
    (fun _=>runtime_demands prims ctx so rs i acc out h R gb hg)
end ZkFormal.NearV3.Candidates.ProcNativeForwardCodec
