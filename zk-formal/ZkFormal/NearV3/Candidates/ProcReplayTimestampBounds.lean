import ZkFormal.NearV3.Candidates.ProcReplayTimestampRounds
import ZkFormal.NearV3.Candidates.ProcConvertedPointers
import ZkFormal.NearV3.Candidates.ProcPreparedSequence
namespace ZkFormal.NearV3.Candidates.ProcReplayTimestampBounds
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
open ProcRequestPointers ProcReplayTimestampRounds

theorem model_entry (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hs:Small reqs) (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h:processEv n allowed reqs st0 fuel=.ok (st,rs))
    (rd : Round) (hr:rd∈rs) (e : Step) (he:e∈rd.steps) :
    reqs.length≤e.t ∧ e.t-reqs.length<64*reqs.length := by
  have hm:e∈rs.flatMap Round.steps := List.mem_flatMap.mpr ⟨rd,hr,he⟩
  obtain ⟨i,hi,hei⟩:=List.mem_iff_getElem.mp hm
  have ht:=(ProcModelClock.process_clock n allowed reqs st0 st fuel rs h).1 i hi
  rw [hei] at ht
  have hb:=process_entries_bound n allowed reqs hs st0 st fuel rs h
  omega

theorem model_entry_clock (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hs:Small reqs) (hc:reqs.length≤4096) (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h:processEv n allowed reqs st0 fuel=.ok (st,rs))
    (rd : Round) (hr:rd∈rs) (e : Step) (he:e∈rd.steps) :
    T0+(e.t-reqs.length)<1310720 ∧ 2*(T0+(e.t-reqs.length))+1<2^29 := by
  have hb:=model_entry n allowed reqs hs st0 st fuel rs h rd hr e he
  unfold T0
  omega

theorem convRaw_count (p : Params) (n : Nat) (raw : List RawReq) :
    (convRaw p n raw).length≤raw.length := by
  exact List.length_filterMap_le _ _

/-- Prepared requests bound the renamed native clock before actual replay succeeds. -/
theorem prepared_entry (sp : SchedPub) (prev : NearSpec.Bandwidth.State)
    (hs:SchedPubOk sp) (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h:processEv sp.ids.length sp.allowed
      (convRaw sp.params sp.ids.length (instOf sp).raw) st0 fuel=.ok (st,rs))
    (rd : Round) (hr:rd∈rs) (e : Step) (he:e∈rd.steps) :
    T0+(e.t-(convRaw sp.params sp.ids.length (instOf sp).raw).length)<1310720 ∧
    2*(T0+(e.t-(convRaw sp.params sp.ids.length (instOf sp).raw).length))+1<2^29 := by
  have hi:=(ProcPreparedSequence.input_bounds sp prev hs).2.2
  have hc:=convRaw_count sp.params sp.ids.length (instOf sp).raw
  apply model_entry_clock _ _ _ (ProcConvertedPointers.convRaw_small _ _ _) (by
    change (instOf sp).raw.length≤4096 at hi
    omega) _ _ _ _ h rd hr e he
end ZkFormal.NearV3.Candidates.ProcReplayTimestampBounds
