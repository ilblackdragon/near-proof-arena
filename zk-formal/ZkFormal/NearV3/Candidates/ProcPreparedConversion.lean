import ZkFormal.NearV3.Candidates.ProcPreparedBitmaps
import ZkFormal.NearV3.Candidates.ProcConversionExact
namespace ZkFormal.NearV3.Candidates.ProcPreparedConversion
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

theorem rawOf_bits (sp : SchedPub) (hb : ProcPreparedBitmaps.PubBits sp)
    (q : RawReq) (hq : q∈rawOf sp.ids sp.raw) : q.bm.length=5 := by
  simp only [rawOf,List.mem_flatMap,List.mem_filterMap] at hq
  obtain ⟨⟨sender,brs⟩,he,br,hr,hq⟩ := hq
  split at hq <;> cases hq
  exact hb (sender,brs) he br hr

theorem input_valid {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint=.ok p)
    (sp : SchedPub) (hsp : sp∈p.sched) (prev : NearSpec.Bandwidth.State) :
    ProcConversionSuccess.RawValid (ProcPreparedSequence.input sp prev) := by
  intro q hq
  have hr := (prepD0_rawOk hp sp hsp).raw q hq
  have hb := rawOf_bits sp (ProcPreparedBitmaps.prepD0_bits hp sp hsp) q (List.mem_filter.mp hq).1
  exact ⟨hb,hr.1,hr.2.1⟩

/-- Every actual prepared input passes the full conversion phase: generation,
convRaw consistency and the generator's request-count guard. -/
theorem prepared_conversion {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint=.ok p)
    (sp : SchedPub) (hsp : sp∈p.sched) (prev : NearSpec.Bandwidth.State) :
    let I := ProcPreparedSequence.input sp prev
    ∃out : Array CReq,
      forIn I.raw #[] (ProcConverted.step I)=.ok out ∧
      convRaw I.p I.ids.length I.raw=ProcConversionExact.view out ∧
      Gen.check (convRaw I.p I.ids.length I.raw==ProcConversionExact.view out) "convRaw differs"=.ok () ∧
      Gen.check (out.size<65536) "too many requests"=.ok () ∧ out.size≤4096 := by
  dsimp only
  obtain ⟨out,ho,he,hc⟩ := ProcConversionExact.conversion_exact _ (input_valid hp sp hsp prev)
  have hi := ProcPreparedSequence.input_bounds sp prev (prepD0_sched hp sp hsp)
  have hb : out.size≤4096 := by omega
  refine ⟨out,ho,he,?_,?_,hb⟩
  · simp [he,Gen.check,pure,Except.pure]
  · have hl : out.size<65536 := by omega
    simp [Gen.check,hl,pure,Except.pure]
end ZkFormal.NearV3.Candidates.ProcPreparedConversion
