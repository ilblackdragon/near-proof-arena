import ZkFormal.NearV3.Candidates.ProcCodecExecutionIndex
namespace ZkFormal.NearV3.Candidates.ProcCodecExecutionFieldPrefix
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecExecutionTrace ProcCodecExecutionIndex

theorem to_loop {α σ ε : Type} {step : α→σ→Except ε (ForInStep σ)}
    {xs : List α} {s out : σ} (h : Steps step xs s out) : forIn xs s step=.ok out := by
  induction h with
  | nil => rfl
  | cons he ht ih => simp only [List.forIn_cons,he,bind,Except.bind,ih]

theorem field (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f : Nat) (hf : f<3)
    (s out : RecordState)
    (h : fieldStep I R present vid gb fwd k f s=.ok (.yield out))
    (g : Nat) (hg : g<8) :
    ∃before after suffix,
      forIn (List.range g) (s.1,s.2,0,0,0,0)
        (fun j st=>ProcPriorCodecRecordStep.step I R present gb fwd
          (ProcPriorCodecNativeHash.instanceCells I R present vid) k f j st)=.ok before ∧
      ProcPriorCodecRecordStep.step I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vid)
        k f g before=.ok (.yield after) ∧
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
    obtain ⟨before,after,hpre,hstep,hpost⟩ := at_index _ _ st hs g (by simpa using hg)
    have hw : ∀j∈List.range 8,∀before after,
        ProcPriorCodecRecordStep.step I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vid) k f j before=.ok (.yield after)→
        ∃added,after.1.toList=before.1.toList++added ∧ added.length=1 := by
      intro j hj before after hstep
      obtain ⟨result,added,hy,hr,hl,_⟩ := byte_step_quiet I R present vid gb fwd k f j hf (List.mem_range.mp hj) before (.yield after) hstep
      cases hy
      exact ⟨added,hr,hl⟩
    obtain ⟨pre,hpr,hpl⟩ := span (fun s : ProcPriorCodecRecordStep.State=>s.1.toList) 1 _ _ before hpre
      (fun j hj=>hw j (List.mem_of_mem_take hj))
    obtain ⟨post,hpo,_⟩ := span (fun s : ProcPriorCodecRecordStep.State=>s.1.toList) 1 _ after st hpost
      (fun j hj=>hw j (List.mem_of_mem_drop hj))
    refine ⟨before,after,post,?_,?_,?_,hpo⟩
    · simpa only [List.take_range,Nat.min_eq_left (show g≤8 by omega)] using to_loop hpre
    · simpa only [List.getElem_range] using hstep
    · have hh := congrArg List.length hpr
      simp only [Array.length_toList,List.length_append,List.length_take,List.length_range,hpl,
        Nat.one_mul,Nat.min_eq_left (show g≤8 by omega)] at hh
      exact hh
end ZkFormal.NearV3.Candidates.ProcCodecExecutionFieldPrefix
