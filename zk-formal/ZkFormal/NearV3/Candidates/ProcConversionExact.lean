import ZkFormal.NearV3.Candidates.ProcConversionSuccess
namespace ZkFormal.NearV3.Candidates.ProcConversionExact
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def view (cv : Array CReq) : List NearSpecV3.Scheduler.Req :=
  cv.toList.map (fun c=>⟨c.link,c.incs⟩)

theorem step_view (I : Input) (q : RawReq) (cv : Array CReq)
    (out : ForInStep (Array CReq)) (h : ProcConverted.step I q cv=.ok out) :
    ∃next,out=.yield next ∧ view next=view cv++convRaw I.p I.ids.length [q] := by
  cases hb : setBits q.bm with
  | nil =>
    simp only [ProcConverted.step,hb,List.isEmpty_nil,ite_true,pure,Except.pure,Except.ok.injEq] at h
    subst out
    exact ⟨cv,rfl,by simp [convRaw,incsOf,hb,incsFrom]⟩
  | cons c cs =>
    simp only [ProcConverted.step,hb,List.isEmpty_cons,Bool.false_eq_true,ite_false] at h
    simp only [bind,Except.bind,pure,Except.pure] at h
    repeat first | cases h | split at h
    all_goals exact ⟨_,rfl,by simp [view,convRaw,incsOf,hb,incsFrom]⟩

theorem loop_view (I : Input) (qs : List RawReq) (cv out : Array CReq)
    (h : forIn qs cv (ProcConverted.step I)=.ok out) :
    view out=view cv++convRaw I.p I.ids.length qs := by
  induction qs generalizing cv with
  | nil => simp only [List.forIn_nil] at h; cases h; simp [convRaw]
  | cons q qs ih =>
    rw [List.forIn_cons] at h
    cases he : ProcConverted.step I q cv with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok s =>
      rcases step_view I q cv s he with ⟨next,rfl,hn⟩
      simp only [he,bind,Except.bind] at h
      rw [ih next h,hn]
      cases hx : incsOf I.p q.bm <;> simp [convRaw,hx,List.append_assoc]

theorem conversion_exact (I : Input) (h : ProcConversionSuccess.RawValid I) :
    ∃out,forIn I.raw #[] (ProcConverted.step I)=.ok out ∧
      convRaw I.p I.ids.length I.raw=view out ∧ out.size≤I.raw.length := by
  obtain ⟨out,ho,hc⟩ := ProcConversionSuccess.conversion_success I h
  exact ⟨out,ho,by simpa [view] using (loop_view I I.raw #[] out ho).symm,hc⟩
end ZkFormal.NearV3.Candidates.ProcConversionExact
