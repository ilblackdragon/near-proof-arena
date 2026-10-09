import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulator
import ZkFormal.NearV3.Candidates.SchedSetAll
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorRows
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcPriorCodecRecordStep
open ProcPriorCodecExtra ProcPriorCodecAssignments

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000 in
theorem cells (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k g : Nat) (s out : State) (hg : g<8)
    (h : step I R present gb fwd inst k 2 g s=.ok (.yield out)) :
    ∃row, out.1=s.1.push row ∧ row[Codec.ap]! = s.2.2.1 ∧
      row[Codec.apost]! = s.2.2.2.1 ∧ row[Codec.big]! = s.2.2.2.2.1 := by
  have hh : g=0 ∨ g=1 ∨ g=2 ∨ g=3 ∨ g=4 ∨ g=5 ∨ g=6 ∨ g=7 := by omega
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [step,check,bind,Except.bind,pure,Except.pure] at h
  iterate 4
    all_goals repeat first | split at h | cases h
  all_goals try subst out
  all_goals try (simp only [Except.ok.injEq,ForInStep.yield.injEq] at h; subst out)
  all_goals refine ⟨_,rfl,?_,?_,?_⟩
  all_goals unfold recordRow
  all_goals rw [SchedSetAll.cell _ _ _ (by decide)]
  all_goals simp [SchedSetAll.lookup,List.foldl_append,baseExtra,allowanceExtra,priorExtra,
    wrapExtra,compareExtra,carryExtra,endExtra,forwardExtra,
    Codec.ap,Codec.apost,Codec.big,Codec.lowf,Codec.wt,Codec.nzb,Codec.ib,Codec.ig2,Codec.e2,
    Codec.cb,Codec.rend,Codec.bF,Codec.a1,Codec.a2,Codec.g2,Codec.al,Codec.base,Codec.afin,
    Codec.gfin,Codec.u0g,Codec.fwg,Codec.cx,Codec.cy,Codec.cbit,Codec.cg,Codec.pm0,Codec.pm1,
    Codec.fb,Codec.apR,Codec.bigR,Codec.a0g]
end ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorRows
