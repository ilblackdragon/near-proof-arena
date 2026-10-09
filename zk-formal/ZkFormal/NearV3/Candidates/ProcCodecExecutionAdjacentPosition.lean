import ZkFormal.NearV3.Candidates.ProcCodecExecutionAdjacentIndex
namespace ZkFormal.NearV3.Candidates.ProcCodecExecutionAdjacentPosition
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecExecutionTrace ProcCodecExecutionAdjacentIndex
 theorem field_pair (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f : Nat) (hf : f<3)
    (s out : RecordState)
    (h : fieldStep I R present vid gb fwd k f s=.ok (.yield out))
    (g : Nat) (hg : g<7) :
    ∃before mid after suffix,
      ProcPriorCodecRecordStep.step I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vid)
        k f g before=.ok (.yield mid) ∧
      ProcPriorCodecRecordStep.step I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vid)
        k f (g+1) mid=.ok (.yield after) ∧
      before.1.size=s.1.size+g ∧ out.1.toList=after.1.toList++suffix := by
  unfold fieldStep at h
  cases he : forIn (List.range 8) (s.1,s.2,0,0,0,0)
    (fun g st=>ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g st) with
  | error e => simp only [he,bind,Except.bind] at h; cases h
  | ok st =>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at h
    subst out
    have hs := field_execution I R present vid gb fwd k f hf _ st he
    have hi := pair_span (fun s : ProcPriorCodecRecordStep.State=>s.1.toList) 1 _ _ st hs
      (fun g hg before after hstep=> by
        obtain ⟨result,added,hy,hr,hl,_⟩ := byte_step_quiet I R present vid gb fwd k f g hf (List.mem_range.mp hg) before (.yield after) hstep
        cases hy
        exact ⟨added,hr,hl⟩) g (by simp; omega)
    simpa only [List.getElem_range,Array.length_toList,Nat.one_mul] using hi
end ZkFormal.NearV3.Candidates.ProcCodecExecutionAdjacentPosition
