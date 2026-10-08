import ZkFormal.NearV3.Candidates.ProcPoppedSuccess
namespace ZkFormal.NearV3.Candidates.ProcPreparedRequestGood
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler

theorem converted_good (p : Params) (n : Nat) (raw : List RawReq)
    (hp : Params.calculate Config.pv86 n=some p) :
    ProcPoppedSuccess.GoodRequests (convRaw p n raw) := by
  intro q hq
  obtain ⟨r,hr,hq⟩ := List.mem_filterMap.mp hq
  cases hi : incsOf p r.bm with
  | nil => simp [hi] at hq
  | cons x xs =>
    simp only [hi,Option.some.injEq] at hq
    subst q
    have hb := incsOf_length_le p r.bm
    rw [hi] at hb
    refine ⟨by change (x::xs).length<64; omega,?_⟩
    intro inc hinc
    have hh := incsOf_ge p r.bm inc (hi ▸ hinc)
    have hk := (pv86_kappa hp).1
    omega

/-- Every starting invariant for native bucket construction comes from the
actual prepared request list, including A8 distinct links and PV86 positivity. -/
theorem prepared_initial (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) :
    let I := ProcPreparedSequence.input sp prev
    let reqs := convRaw I.p I.ids.length I.raw
    let st := ProcCoreReplay.initial I
    let ps := (ProcModelStep.initial reqs st).1
    ProcPoppedSuccess.GoodRequests reqs ∧
    ProcPendingCurrent.Current reqs st.al ps ∧
    (ps.map (fun p=>ProcPendingCurrent.link reqs p.v)).Nodup ∧
    (∀p∈ps,ProcRequestPointers.Valid reqs p.v) ∧
    ProcPendingTime.Inv ps reqs.length :=
  ⟨converted_good sp.params sp.ids.length (instOf sp).raw hs.params,
    ProcPreparedLinks.prepared_initial_current sp prev,
    ProcInitialLinks.prepared_initial_nodup sp hs prev,
    ProcRequestPointers.initial_valid _ _,ProcPendingTime.initial _ _⟩
end ZkFormal.NearV3.Candidates.ProcPreparedRequestGood
