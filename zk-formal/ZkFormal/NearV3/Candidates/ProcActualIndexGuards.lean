import ZkFormal.NearV3.Candidates.ProcShufflePointers
import ZkFormal.NearV3.Candidates.ProcActualPrefix
namespace ZkFormal.NearV3.Candidates.ProcActualIndexGuards
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

/-- Request-pointer validity transports to the exact converted CReq array. -/
theorem view_bounds (cv : Array CReq) (v : Nat)
    (hv : ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v) :
    v/64<cv.size ∧ v%64<cv[v/64]!.incs.length := by
  have hi : v/64<cv.size := by simpa [ProcActualConversionExact.view] using hv.1
  refine ⟨hi,?_⟩
  have hj := hv.2
  simpa [ProcActualConversionExact.view,List.getElem!_toArray,getElem!_def,hi] using hj

theorem index_checks (cv : Array CReq) (v : Nat)
    (hv : ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v) :
    check (v/64<cv.size) "entry cid"=.ok () ∧
    check (v%64<cv[v/64]!.incs.length) "entry j"=.ok () := by
  obtain ⟨hi,hj⟩ := view_bounds cv v hv
  simp only [check,hi,hj,decide_true,ite_true,pure,Except.pure,and_self]

/-- Every shuffled entry of a successful prepared process passes both actual
replay index checks against its converted request array. -/
theorem prepared_checks (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (st : PState) (rs : List Round) (cv : Array CReq)
    (hcv : convRaw sp.params sp.ids.length (instOf sp).raw=ProcActualConversionExact.view cv)
    (h : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∀rd∈rs,∀v∈rd.shuffled,
      check (v/64<cv.size) "entry cid"=.ok () ∧
      check (v%64<cv[v/64]!.incs.length) "entry j"=.ok () := by
  have hg := ProcPreparedRequestGood.converted_good _ _ (instOf sp).raw hs.params
  have hp := ProcShufflePointers.process_pointers sp.ids.length sp.allowed
    (convRaw sp.params sp.ids.length (instOf sp).raw)
    (fun q hq=>Nat.le_of_lt (hg q hq).1) _ st _ rs h
  intro rd hrd v hv
  apply index_checks
  rw [←hcv]
  exact (hp rd hrd).2 v hv
/-- The actual bucket-indexed lookup is in range and passes both index checks. -/
theorem prepared_indexed (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (st : PState) (rs : List Round) (cv : Array CReq)
    (hcv : convRaw sp.params sp.ids.length (instOf sp).raw=ProcActualConversionExact.view cv)
    (h : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (rd : Round) (hrd : rd∈rs) (x : Nat) (hx : x<rd.bucket.length) :
    x<rd.shuffled.length ∧
    check (rd.shuffled[x]!/64<cv.size) "entry cid"=.ok () ∧
    check (rd.shuffled[x]!%64<cv[rd.shuffled[x]!/64]!.incs.length) "entry j"=.ok () := by
  have hg := ProcPreparedRequestGood.converted_good _ _ (instOf sp).raw hs.params
  have hp := ProcShufflePointers.process_pointers sp.ids.length sp.allowed
    (convRaw sp.params sp.ids.length (instOf sp).raw)
    (fun q hq=>Nat.le_of_lt (hg q hq).1) _ st _ rs h
  have hxs : x<rd.shuffled.length := by rw [(hp rd hrd).1]; exact hx
  refine ⟨hxs,prepared_checks sp hs prev st rs cv hcv h rd hrd _ ?_⟩
  rw [getElem!_pos rd.shuffled x hxs]
  exact List.getElem_mem hxs

end ZkFormal.NearV3.Candidates.ProcActualIndexGuards
