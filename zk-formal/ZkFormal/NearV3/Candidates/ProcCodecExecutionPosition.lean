import ZkFormal.NearV3.Candidates.ProcCodecExecutionIndex
namespace ZkFormal.NearV3.Candidates.ProcCodecExecutionPosition
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecExecutionTrace ProcCodecExecutionIndex

 theorem block (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (s out : RecordState)
    (h : forIn (List.range (R.n*R.n)) s (blockStep I R present vid gb fwd)=.ok out)
    (k : Nat) (hk : k<R.n*R.n) :
    ∃before after added suffix,
      blockStep I R present vid gb fwd k before=.ok (.yield after) ∧
      before.1.size=s.1.size+24*k ∧ after.1.toList=before.1.toList++added ∧
      added.length=24 ∧ out.1.toList=after.1.toList++suffix := by
  have hs := blocks_execution I R present vid gb fwd s out h
  have hi := indexed_span (fun s : RecordState=>s.1.toList) 24 _ s out hs
    (fun k _ before after hstep=> by
      obtain ⟨result,added,he,hr,hl,_⟩ := block_step_quiet I R present vid gb fwd k before (.yield after) hstep
      cases he
      exact ⟨added,hr,hl⟩) k (by simpa using hk)
  simpa only [List.getElem_range,Array.length_toList] using hi

 theorem field (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k : Nat) (s out : RecordState)
    (h : blockStep I R present vid gb fwd k s=.ok (.yield out))
    (f : Nat) (hf : f<3) :
    ∃before after added suffix,
      fieldStep I R present vid gb fwd k f before=.ok (.yield after) ∧
      before.1.size=s.1.size+8*f ∧ after.1.toList=before.1.toList++added ∧
      added.length=8 ∧ out.1.toList=after.1.toList++suffix := by
  unfold blockStep at h
  cases he : forIn (List.range 3) s (fieldStep I R present vid gb fwd k) with
  | error e => simp only [he,bind,Except.bind] at h; cases h
  | ok st =>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at h
    subst out
    have hs := record_execution I R present vid gb fwd k s st he
    have hi := indexed_span (fun s : RecordState=>s.1.toList) 8 _ s st hs
      (fun f hf before after hstep=> by
        obtain ⟨result,added,hy,hr,hl,_⟩ := field_step_quiet I R present vid gb fwd k f (List.mem_range.mp hf) before (.yield after) hstep
        cases hy
        exact ⟨added,hr,hl⟩) f (by simpa using hf)
    simpa only [List.getElem_range,Array.length_toList] using hi

 theorem byte (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f : Nat) (hf : f<3)
    (s out : RecordState)
    (h : fieldStep I R present vid gb fwd k f s=.ok (.yield out))
    (g : Nat) (hg : g<8) :
    ∃before after added suffix,
      ProcPriorCodecRecordStep.step I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vid)
        k f g before=.ok (.yield after) ∧
      before.1.size=s.1.size+g ∧ after.1.toList=before.1.toList++added ∧
      added.length=1 ∧ out.1.toList=after.1.toList++suffix := by
  unfold fieldStep at h
  cases he : forIn (List.range 8) (s.1,s.2,0,0,0,0)
    (fun g st=>ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g st) with
  | error e => simp only [he,bind,Except.bind] at h; cases h
  | ok st =>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at h
    subst out
    have hs := field_execution I R present vid gb fwd k f hf _ st he
    have hi := indexed_span (fun s : ProcPriorCodecRecordStep.State=>s.1.toList) 1 _ _ st hs
      (fun g hg before after hstep=> by
        obtain ⟨result,added,hy,hr,hl,_⟩ := byte_step_quiet I R present vid gb fwd k f g hf (List.mem_range.mp hg) before (.yield after) hstep
        cases hy
        exact ⟨added,hr,hl⟩) g (by simpa using hg)
    simpa only [List.getElem_range,Array.length_toList,Nat.one_mul] using hi
end ZkFormal.NearV3.Candidates.ProcCodecExecutionPosition
