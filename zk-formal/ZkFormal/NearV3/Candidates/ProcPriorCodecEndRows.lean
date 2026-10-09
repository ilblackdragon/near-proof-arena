import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulator
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeHash
import ZkFormal.NearV3.Candidates.SchedSetAll
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecEndRows
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcPriorCodecRecordStep
open ProcPriorCodecExtra ProcPriorCodecAssignments

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000 in
theorem cells (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k : Nat) (s out : State) (hk : k<R.n*R.n)
    (h : step I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vidV) k 2 7 s=.ok (.yield out)) :
    ∃row, out.1=s.1.push row ∧
      row[Codec.a1]! =ProcPriorCodecEndArithmetic.credited I R present k s.2.2.2.2.2 ∧
      row[Codec.a2]! =ProcPriorCodecRecordTotal.endAllowance I R present k s.2.2.2.2.2 ∧
      row[Codec.g2]! =b2n I.allowed[k]!*I.p.base ∧
      row[Codec.afin]! =(R.segs.getD k default).vfin ∧
      row[Codec.al]! =b2n I.allowed[k]! ∧ row[Codec.base]! =I.p.base ∧
      row[Codec.rend]! =1 ∧ row[Codec.bF]! =(if s.2.2.2.2.1=1 then 1 else 0) := by
  all_goals simp [step,check,bind,Except.bind,pure,Except.pure,getElem!_pos,hk] at h
  iterate 4
    all_goals repeat first | split at h | cases h
  all_goals try subst out
  all_goals try (simp only [Except.ok.injEq,ForInStep.yield.injEq] at h; subst out)
  all_goals refine ⟨_,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals unfold recordRow
  all_goals rw [SchedSetAll.cell _ _ _ (by decide)]
  all_goals simp [SchedSetAll.lookup,List.foldl_append,baseExtra,allowanceExtra,priorExtra,
    wrapExtra,compareExtra,carryExtra,endExtra,forwardExtra,
    Codec.ap,Codec.apost,Codec.big,Codec.lowf,Codec.wt,Codec.nzb,Codec.ib,Codec.ig2,Codec.e2,
    Codec.cb,Codec.rend,Codec.bF,Codec.a1,Codec.a2,Codec.g2,Codec.al,Codec.base,Codec.afin,
    Codec.gfin,Codec.u0g,Codec.fwg,Codec.cx,Codec.cy,Codec.cbit,Codec.cg,Codec.pm0,Codec.pm1,
    Codec.fb,Codec.apR,Codec.bigR,Codec.a0g,Codec.bpre,Codec.bpost,
    Codec.kR,Codec.pos,Codec.vbg,Codec.kidx,Codec.klo,Codec.khi,Codec.fS,Codec.fR,Codec.fA,
    Codec.g,Codec.ig7,Codec.e7,Codec.ikl,Codec.ekl,Codec.pbit,Codec.rs,Codec.gb,Codec.srcC,
    Codec.hasC,Codec.useC,ProcPriorCodecAccumulator.postByte,List.range_succ,ProcPriorCodecEndArithmetic.credited,
    ProcPriorCodecRecordTotal.endAllowance,ProcPriorCodecNativeHash.instanceCells,Codec.act,
    Codec.tau,Codec.pres,Codec.vid,Codec.nn,Codec.NN,Codec.fair,Codec.itz,Codec.zt, *]
end ZkFormal.NearV3.Candidates.ProcPriorCodecEndRows
