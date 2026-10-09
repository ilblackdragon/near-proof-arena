import ZkFormal.NearV3.Candidates.ProcModelPointers
import ZkFormal.NearV3.Candidates.ProcConvertedLinks
namespace ZkFormal.NearV3.Candidates.ProcConvertedPointers
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcRequestPointers

theorem convRaw_small (p : NearSpecV3.Scheduler.Params) (n : Nat) (raw : List RawReq) :
    Small (convRaw p n raw) := by
  intro q hq
  obtain ⟨r,hr,hq⟩ := List.mem_filterMap.mp hq
  cases hi : incsOf p r.bm with
  | nil => simp [hi] at hq
  | cons x xs =>
    simp only [hi,Option.some.injEq] at hq
    subst q
    have hb := incsOf_length_le p r.bm
    rw [hi] at hb
    change (x::xs).length≤64
    omega

theorem view_small (I : Input) (cv : Array CReq)
    (hc : forIn I.raw #[] (ProcConverted.step I)=.ok cv) : Small (ProcConversionExact.view cv) := by
  intro q hq
  obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hq
  have hf := ProcConvertedFacts.loop_facts I cv hc c hc'
  change c.incs.length≤64
  rw [hf.2.2]
  have := incsOf_length_le I.p c.bm
  omega

/-- Actual conversion and model execution discharge both request-ID and
increase-index guards at every emitted entry, without a per-entry premise. -/
theorem model_index_guards (I : Input) (cv : Array CReq)
    (hc : forIn I.raw #[] (ProcConverted.step I)=.ok cv)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv I.ids.length I.allowed (ProcConversionExact.view cv) st0 fuel=.ok (st,rs))
    (rd : Round) (hr : rd∈rs) (e : Step) (he : e∈rd.steps) :
    e.v/64<cv.size ∧ e.v%64<cv[e.v/64]!.incs.length := by
  have hv := ProcModelPointers.process_pointers _ _ _ (view_small I cv hc) _ _ _ _ h rd hr e he
  have hi : e.v/64<cv.size := by simpa [ProcConversionExact.view] using hv.1
  refine ⟨hi,?_⟩
  have hh := hv.2
  rw [ProcConvertedLinks.view_get cv _ hi] at hh
  exact hh

theorem model_index_checks (I : Input) (cv : Array CReq)
    (hc : forIn I.raw #[] (ProcConverted.step I)=.ok cv)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv I.ids.length I.allowed (ProcConversionExact.view cv) st0 fuel=.ok (st,rs))
    (rd : Round) (hr : rd∈rs) (e : Step) (he : e∈rd.steps) :
    check (e.v/64<cv.size) "cid"=.ok () ∧
    check (e.v%64<cv[e.v/64]!.incs.length) "increase index"=.ok () := by
  obtain ⟨hi,hj⟩ := model_index_guards I cv hc st0 st fuel rs h rd hr e he
  simp only [check,hi,hj,decide_true,ite_true,pure,Except.pure,and_self]
end ZkFormal.NearV3.Candidates.ProcConvertedPointers
